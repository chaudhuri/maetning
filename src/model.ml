(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2016  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

let collapse_steps       = true (* collapse steps that have the same constraints *)
let elide_true_nonatoms  = true (* omit T A when A is a non-atom *)
let elide_dead           = true (* omit T* A when A is a non-atom *)
let elide_false          = true (* omit F A *)
let elide_false_nonatoms = true (* omit F A when A is a non-atom *)

(* Model reconstruction based on the algorithm described in:

   Taus Brock-Nannestad and Kaustuv Chaudhuri, "Saturation-based
   Countermodel Construction for Propositional Intuitionistic Logic",
   2016
*)

open Batteries
module Ft = FingerTree

open Idt
open Term
open Form
open Sequent
open Inverse

open Debug

type model = {
  constr : constr ;
  kids   : model list ;
}

and constr = {
  live : form list ;            (* all T *)
  dead : form list ;            (* all T *)
  fals : form option ;          (* all F *)
}

(******************************************************************************)

let model_kids modl = modl.kids

exception Nonatomic

let form_id lforms f =
  match f.form with
  | Atom (_, l, []) -> begin
      match List.find (fun lf -> lf.label == l) lforms with
      | _ -> raise Nonatomic
      | exception Not_found -> l
    end
  | _ -> raise Nonatomic

let true_ids lforms constr =
  List.fold_left begin fun set f ->
    match form_id lforms f with
    | id -> IdtSet.add id set
    | exception Nonatomic -> set
  end IdtSet.empty (constr.live @ constr.dead)

let model_compatible lforms constr modl =
  IdtSet.equal
    (true_ids lforms constr)
    (true_ids lforms modl.constr)

let fork lforms constr kids =
  if collapse_steps && List.for_all (model_compatible lforms constr) kids then
    let kids = kids |> List.map model_kids |> List.concat in
    { constr ; kids }
  else
    { constr ; kids }

(******************************************************************************)

exception Model

let first_order () =
  Format.eprintf "Cannot construct countermodels for first-order formulas@." ;
  raise Model

let format_form_expanded lforms ff f =
  let rec expand f =
    match f.form with
    | Atom (_, l, []) -> begin
        match List.find (fun lf -> lf.label == l) lforms with
        | lf -> expand lf.Form.skel
        | exception Not_found -> f
      end
    | And (pol, f1, f2) -> conj ~pol [expand f1 ; expand f2]
    | True _ -> f
    | Or (f1, f2) -> disj [expand f1 ; expand f2]
    | False -> f
    | Implies (f1, f2) -> implies [expand f1] (expand f2)
    | Forall _ | Exists _ | Atom _ -> first_order ()
    | Shift f -> shift (expand f)
  in
  format_form () ff (expand f)

(* let format_form_expanded lforms ff f = format_form () ff f *)

let compound lforms f =
  match f.form with
  | Atom (_, l, _) ->
      List.exists (fun lf -> lf.label == l) lforms
  | _ -> true

let format_constr lforms ff constr =
  let open Format in
  pp_open_box ff 2 ; begin
    let live = List.filter_map begin fun f ->
        if elide_true_nonatoms && compound lforms f then None
        else Some (fun () -> fprintf ff "T @[%a@]" (format_form_expanded lforms) f)
      end constr.live in
    let dead = List.filter_map begin fun f ->
        if elide_dead && compound lforms f then None
        else Some (fun () -> fprintf ff "T* @[%a@]" (format_form ()) f)
      end constr.dead in
    let fals =
      if elide_false then [] else
      match constr.fals with
      | Some f ->
          if elide_false_nonatoms && compound lforms f then []
          else [fun () -> fprintf ff "F @[%a@]" (format_form_expanded lforms) f]
      | None -> []
    in
    (live @ dead @ fals) |>
    List.interleave (fun () -> fprintf ff ",@ ") |>
    List.iter (fun doit -> doit ())
  end ; pp_close_box ff ()

let pp_indent ff n =
  for i = 1 to n do
    Format.pp_print_string ff "  "
  done

let rec format_model_lines lforms indent ff modl =
  let open Format in
  List.iter (format_model_lines lforms (indent + 1) ff) modl.kids ;
  fprintf ff "%a* @[%a@]@," pp_indent indent (format_constr lforms) modl.constr

let format_model lforms ff modl =
  Format.fprintf ff "@[<v0>%a@]" (format_model_lines lforms 0) modl

let dot_format_model lforms modl =
  let open Format in
  let (ic, oc) = Unix.open_process "dot -Tsvg" in
  let dotff = formatter_of_output oc in
  Format.pp_set_margin dotff max_int ;
  fprintf dotff "digraph countermodel {@.rankdir=BT;@." ;
  let cur_world = ref (-1) in
  let next_world () = incr cur_world ; !cur_world in
  let rec spin_lines modl =
    let w = next_world () in
    let ws = List.map spin_lines modl.kids in
    fprintf dotff "w%d [shape=box,fontname=\"monospace\",fontsize=10,label=\"@[%a@]\"];@."
      w (format_constr lforms) modl.constr ;
    List.iter (fun u -> fprintf dotff "w%d -> w%d;" w u) ws ;
    w in
  ignore (spin_lines modl) ;
  fprintf dotff "}@." ;
  close_out oc ;
  let result = BatIO.read_all ic in
  let start = String.find result "<svg " in
  let result = String.sub result start (String.length result - start) in
  ignore (Unix.close_process (ic, oc)) ;
  result

let query lforms constr =
  let base ~stored right =
    let sq = mk_sequent ()
        ~left:(stored |>
               List.map (fun l -> (l, [])) |>
               Ft.of_list)
        ?right:(right |> Option.map (fun l -> (l, [])))
    in
    dprintf "modelquery" "Need to check: @[%a@]@." (format_sequent ()) sq ;
    let subs = Inverse.Data.subsumes sq in
    dprintf "modelquery" "Was %ssubsumed@." (if subs then "" else "NOT ") ;
    subs
  in
  let rec right_active ~stored right =
    match right with
    | None -> base ~stored None
    | Some rf -> begin
        match rf.form with
        | Atom (_, l, [])
        | Shift {form = Atom (_, l, []) ; _} ->
            base ~stored (Some l)
        | And (_, rf1, rf2) ->
            right_active ~stored (Some rf1) &&
            right_active ~stored (Some rf2)
        | True _ ->
            true
        | Or (rf1, rf2) ->
            right_active ~stored (Some rf1) ||
            right_active ~stored (Some rf2)
        | False ->
            false
        | Implies (rf1, rf2) ->
            left_active ~stored ~left:[rf1] (Some rf2)
        | Forall _ | Exists _ | Atom _ -> first_order ()
        | Shift rf ->
            right_active ~stored (Some rf)
        (* | Shift _ -> *)
        (*     Debug.bugf "Model.query(right_active}: Impossible @[%a@]" *)
        (*       (format_form ()) rf *)
      end
  and left_active ~stored ~left right =
    match left with
    | [] -> right_active ~stored right
    | lf :: left -> begin
        match lf.form with
        | Atom (_, l, [])
        | Shift {form = Atom (_, l, []) ; _} ->
            left_active ~stored:(l :: stored) ~left right
        | And (_, lf1, lf2) ->
            left_active ~stored ~left:(lf1 :: lf2 :: left) right
        | True _ ->
            left_active ~stored ~left right
        | Or (lf1, lf2) ->
            left_active ~stored ~left:(lf1 :: left) right &&
            left_active ~stored ~left:(lf2 :: left) right
        | False ->
            true
        | Implies _ ->
            (* We just drop this assumption, i.e., try just weakening *)
            left_active ~stored ~left right
        | Forall _ | Exists _ | Atom _ -> first_order ()
        | Shift lf ->
            left_active ~stored ~left:(lf :: left) right
        (* | Shift _ -> *)
        (*     Debug.bugf "Model.query(left_active}: Impossible @[%a@]" *)
        (*       (format_form ()) lf *)
      end
  in
  dprintf "modelquery" "Querying @[%a@]@." (format_constr []) constr ;
  let res = left_active ~stored:[] ~left:(constr.live @ constr.dead) constr.fals in
  dprintf "modelquery" "Query was a %s@." (if res then "success" else "failure") ;
  res

let rec simplify_right ~succ ~lforms constr =
  dprintf "model" "simplify_right: @[%a@]@." (format_constr lforms) constr ;
  match constr.fals with
  | None -> simplify_left ~succ ~lforms constr
  | Some rt -> begin
      match rt.form with
      | Atom (_, l, []) -> begin
          match (List.find (fun lf -> lf.label == l) lforms).Form.skel with
          | rt -> simplify_right ~succ ~lforms {constr with fals = Some rt}
          | exception Not_found -> simplify_left ~succ ~lforms constr
        end
      | And (_, rt1, rt2) ->
          let constr1 = {constr with fals = Some rt1} in
          if query lforms constr1 then
            simplify_right ~succ ~lforms {constr with fals = Some rt2}
          else
            simplify_right ~succ ~lforms constr1
      | True _ ->
          succ { constr ; kids = [] }
      | Or (rt1, rt2) ->
          simplify_right ~lforms {constr with fals = Some rt1}
            ~succ:(fun m1 ->
                simplify_right ~lforms {constr with fals = Some rt2}
                  ~succ:(fun m2 ->
                      succ (fork lforms constr [m1 ; m2])))
      | False ->
          simplify_left ~succ ~lforms {constr with fals = None}
      | Implies (rt1, rt2) ->
          simplify_right ~succ ~lforms {
            constr with
            live = rt1 :: constr.live ;
            fals = Some rt2
          }
      | Shift rt ->
          simplify_right ~succ ~lforms {constr with fals = Some rt}
      | Atom _ | Forall _ | Exists _ -> first_order ()
    end

and simplify_left ~succ ~lforms constr =
  dprintf "model" "simplify_left: @[%a@]@." (format_constr lforms) constr ;
  match constr.live with
  | [] ->
      if query lforms constr then
        Debug.bugf "Simplified to true constraint: @[%a@]"
          (format_constr lforms) constr ;
      succ { constr ; kids = [] }
  | lf :: live -> begin
      match lf.form with
      | Atom (_, l, []) -> begin
          match (List.find (fun lf -> lf.label == l) lforms).Form.skel with
          | newlf -> simplify_left ~succ ~lforms {constr with
                                                  dead = lf :: constr.dead ;
                                                  live = newlf :: live}
          | exception Not_found ->
              simplify_left ~succ ~lforms {
                constr with
                live ;
                dead = lf :: constr.dead ;
              }
        end
      | And (_, lf1, lf2) ->
          simplify_left ~succ ~lforms
            {constr with live = lf1 :: lf2 :: live}
      | True _ ->
          simplify_left ~succ ~lforms {constr with live}
      | Or (lf1, lf2) ->
          let constr1 = {constr with live = lf1 :: live} in
          if query lforms constr1 then
            simplify_left ~lforms {constr with live = lf2 :: live} ~succ
          else
            simplify_left ~lforms constr1 ~succ
      | False ->
          succ { constr ; kids = [] }
      | Implies (lf1, lf2) ->
          let constr1 = {live ; dead = lf :: constr.dead ; fals = Some lf1} in
          if query lforms constr1 then
            simplify_left ~lforms ~succ
              { constr with
                dead = lf :: constr.dead ;
                live = lf2 :: live }
          else
            simplify_right ~lforms constr1
              ~succ:(fun m1 -> succ (fork lforms constr [m1]))
      | Shift lf ->
          simplify_left ~lforms ~succ {constr with live = lf :: live}
      | Forall _ | Exists _ | Atom _ -> first_order ()
    end

let create_model res =
  let live = List.filter_map begin fun lf ->
      match lf.place with
      | Left Global | Left Pseudo -> Some lf.Form.skel
      | _ -> None
    end res.lforms in
  let dead = [] in
  let fals = Some res.goal.skel in
  let constr = {live ; dead ; fals} in
  dprintf "model" "Initial constraint: @[%a@]@." (format_constr res.lforms) constr ;
  simplify_right ~lforms:res.lforms ~succ:(fun m -> m) constr
