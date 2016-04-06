(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2016  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

let collapse_steps       = false (* collapse steps that have the same constraints *)
let elide_true_nonatoms  = false (* omit T A when A is a non-atom *)
let elide_dead           = false (* omit T* A when A is a non-atom *)
let elide_false          = false (* omit F A *)
let elide_false_nonatoms = false (* omit F A when A is a non-atom *)

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

exception Model

let first_order () =
  Format.eprintf "Cannot construct countermodels for first-order formulas@." ;
  raise Model

let format_form_expanded lforms ff f =
  let rec expand f =
    match f.form with
    | Atom (_, l, []) -> begin
        match IdtMap.find l lforms with
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

let expose lforms f =
  match f.form with
  | Atom (_, l, args) -> begin
      match List.find (fun lf -> lf.label == l) lforms with
      | lf ->
          let ss = List.fold_right (fun t ss -> Term.Cons (ss, t)) args (Term.Shift 0) in
          app_form ss lf.Form.skel
      | exception Not_found -> f
    end
  | _ -> f

exception Nonatomic

let rec get_atom lforms f =
  match f.form with
  | Atom (_, l, args) -> begin
      match IdtMap.find l lforms with
      | {Form.skel = {Form.form = Atom (_, l, _); _} ; _} -> l
      | _ -> raise Nonatomic
      | exception Not_found -> l
    end
  | Shift f -> get_atom lforms f
  | _ -> raise Nonatomic

let expose_test fn lforms f =
  match f.form with
  | Atom (_, l, args) -> begin
      match List.find (fun lf -> lf.label == l) lforms with
      | lf -> fn lf.Form.skel
      | exception Not_found -> fn f
    end
  | _ -> fn f

let rec compound lforms f =
  match get_atom lforms f with
  | _ -> false
  | exception Nonatomic -> true

let format_constr lforms ff constr =
  let open Format in
  let seen = ref IdtSet.empty in
  let rec see f =
    match get_atom lforms f with
    | l ->
        (* dprintf "modelformat" "Seeing: %s@." l.rep ; *)
        seen := IdtSet.add l !seen
    | exception Nonatomic -> ()
  in
  let is_seen f =
    match get_atom lforms f with
    | l ->
        (* dprintf "modelformat" "%s was seen? %b@." l.rep (IdtSet.mem l !seen) ; *)
        IdtSet.mem l !seen
    | exception Nonatomic -> false
  in
  (* dprintf "modelformat" "constr format start@." ; *)
  pp_open_box ff 2 ; begin
    let live = List.filter_map begin fun f ->
        if elide_true_nonatoms && compound lforms f then None
        else if is_seen f then None
        else (see f ; Some (fun () -> fprintf ff "T @[%a@]" (format_form_expanded lforms) f)) ;
      end (constr.live |> List.unique) in
    let dead = List.filter_map begin fun f ->
        if elide_dead && elide_true_nonatoms && compound lforms f then None
        else if is_seen f then None
        else (see f ; Some (fun () -> fprintf ff "T* @[%a@]" (format_form_expanded lforms) f))
      end (constr.dead |> List.unique) in
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
    List.iter (fun doit -> doit ()) ;
    (* dprintf "modelformat" "constr format end@." ; *)
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


(******************************************************************************)

let model_kids modl = modl.kids

let rec form_id lforms f =
  (* dprintf "modelcompat" "Computing form_id of %a@." (format_form ()) f ; *)
  match f.form with
  | Atom (_, l, []) -> begin
      (* dprintf "modelcompat" "Need to check if %s is non-atomic@." l.rep ; *)
      match IdtMap.find l lforms with
      | {Form.skel = {Form.form = Atom _ ; _} ; _} ->
          (* dprintf "modelcompat" "It BARELY isn't!@." ; *)
          l
      | lf ->
          (* dprintf "modelcompat" "It is: %a@." (format_form ()) lf.Form.skel ; *)
          raise Nonatomic
      | exception Not_found ->
          (* dprintf "modelcompat" "It isn't!@." ; *)
          l
    end
  | Shift f -> form_id lforms f
  | _ ->
      (* dprintf "modelcompat" "Never mind, non-atomic: %a@." (format_form ()) f ; *)
      raise Nonatomic

let true_ids lforms constr =
  List.fold_left begin fun set f ->
    match form_id lforms f with
    | id -> IdtSet.add id set
    | exception Nonatomic -> set
  end IdtSet.empty (constr.live @ constr.dead)

let model_compatible lforms constr modl =
  let ret =
    IdtSet.equal
      (true_ids lforms constr)
      (true_ids lforms modl.constr) in
  (* dprintf "modelcompat" *)
  (*   "@[<v0>%a@,?=@,%a@,: %b@]@." *)
  (*   (format_constr lforms) constr *)
  (*   (format_constr lforms) modl.constr *)
  (*   ret ; *)
  ret

let rec fork lforms constr kids =
  if not collapse_steps then {constr ; kids} else
  let kids =
    if List.for_all (fun kid -> model_compatible lforms constr kid) kids
    then List.map (fun kid -> kid.kids) kids |> List.concat
    else kids
  in
  if kids = [] then {constr ; kids} else
  let rec add_one_kid oldkids newkids modl =
    match newkids with
    | [] -> List.rev_append oldkids [modl]
    | newkid :: newkids ->
        if model_compatible lforms modl.constr newkid then
          List.rev_append oldkids
            (fork lforms newkid.constr (newkid.kids @ modl.kids) :: newkids)
        else add_one_kid (newkid :: oldkids) newkids modl
  in
  let add_one_kid kids modl = add_one_kid [] kids modl in
  let kids = List.fold_left add_one_kid [List.hd kids] (List.tl kids) in
  {constr ; kids}

(******************************************************************************)

let query lforms constr =
  let test_init ~stored right =
    match right with
    | None -> false
    | Some l -> List.mem l stored
  in
  let base ~stored right =
    test_init ~stored right ||
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
  dprintf "modelquery" "Querying @[%a@]@." (format_constr IdtMap.empty) constr ;
  let res = left_active ~stored:[] ~left:(constr.live @ constr.dead) constr.fals in
  dprintf "modelquery" "Query was a %s@." (if res then "success" else "failure") ;
  res

let is_implies f =
  match f.form with
  | Implies _ -> true
  | _ -> false

let is_atomic f =
  match f.form with
  | Atom _ -> true
  | _ -> false

let unique_cons x l =
  let l = List.filter (fun y -> x <> y) l in
  if is_implies x then l @ [x] else x :: l

let add_true_constraints fs constr =
  let fs = List.filter (fun f -> not (List.mem f constr.live || List.mem f constr.dead)) fs in
  if fs = [] then constr else
  let () = List.iter (dprintf "model" "new true %a@." (format_form ())) fs in
  let constr =
    if List.exists is_atomic fs then begin
      let (impls, dead) = List.partition is_implies constr.dead in
      List.iter (dprintf "model" "exhumed: %a@." (format_form ())) impls ;
      {constr with live = impls @ constr.live ; dead}
    end else constr
  in
  let (fs_implies, fs) = List.partition is_implies fs in
  let live = fs @ constr.live @ fs_implies in
  {constr with live}

let rec simplify_right ~succ ~lforms constr =
  dprintf "model" "simplify_right: @[%a@]@." (format_constr IdtMap.empty) constr ;
  match constr.fals with
  | None -> simplify_left ~succ ~lforms ~saved:[] constr
  | Some rt -> begin
      match rt.form with
      | Atom (_, l, []) -> begin
          match (IdtMap.find l lforms).Form.skel with
          | rt -> simplify_right ~succ ~lforms {constr with fals = Some rt}
          | exception Not_found -> simplify_left ~succ ~lforms ~saved:[] constr
        end
      | And (_, rt1, rt2) ->
          let constr1 = {constr with fals = Some rt1} in
          if query lforms constr1 then
            simplify_right ~succ ~lforms {constr with fals = Some rt2}
          else
            simplify_right ~succ ~lforms constr1
      | True _ ->
          succ {constr ; kids = []}
      | Or (rt1, rt2) ->
          simplify_right ~lforms {constr with fals = Some rt1}
            ~succ:(fun m1 ->
                simplify_right ~lforms {constr with fals = Some rt2}
                  ~succ:(fun m2 ->
                      succ (fork lforms constr [m1 ; m2])))
      | False ->
          simplify_left ~succ ~lforms ~saved:[] {constr with fals = None}
      | Implies (rt1, rt2) ->
          simplify_right ~lforms
            ~succ
            (add_true_constraints [rt1] {constr with fals = Some rt2})
      | Shift rt ->
          simplify_right ~succ ~lforms {constr with fals = Some rt}
      | Atom _ | Forall _ | Exists _ -> first_order ()
    end

and simplify_left ~succ ~lforms ~saved constr =
  dprintf "model" "simplify_left: @[%a@]@." (format_constr IdtMap.empty) constr ;
  match constr.live with
  | [] -> begin
      match saved with
      | (_lf, top) :: rest ->
          top ~succ (List.map fst rest)
      | [] ->
          if query lforms constr then
            Debug.bugf "Model: simplified to valid constraint@\n@[%a@]"
              (format_constr lforms) constr
          else succ {constr ; kids = []}
    end
  | lf :: live -> begin
      match lf.form with
      | Atom (_, l, []) -> begin
          match (IdtMap.find l lforms).Form.skel with
          | newlf ->
              {constr with live ; dead = unique_cons lf constr.dead} |>
              add_true_constraints [newlf] |>
              simplify_left ~succ ~lforms ~saved
          | exception Not_found ->
              simplify_left ~succ ~lforms ~saved
                {constr with
                 live ; dead = unique_cons lf constr.dead}
        end
      | And (_, lf1, lf2) ->
          simplify_left ~succ ~lforms ~saved
            (add_true_constraints [lf1 ; lf2] {constr with live})
      | True _ ->
          simplify_left ~succ ~lforms ~saved {constr with live}
      | Or (lf1, lf2) ->
          let constr1 = {constr with live = unique_cons lf1 live} in
          if query lforms constr1 then
            simplify_left ~lforms ~succ ~saved
              (add_true_constraints [lf2]  {constr with live})
          else
            simplify_left ~lforms ~succ ~saved constr1
      | False ->
          succ {constr ; kids = []}
      | Implies (lf1, lf2) ->
          let constr1 = {live ;
                         dead = unique_cons lf constr.dead ;
                         fals = Some lf1} in
          if query lforms constr1 then
            simplify_left ~succ ~lforms ~saved
              (add_true_constraints [lf2] {constr with live})
          else begin
            let save ~succ rest =
              dprintf "model" "Trying saved implication: %a@." (format_form ()) lf ;
              simplify_right ~lforms ~succ:(fun m -> fork lforms constr [m] |> succ)
                {constr1 with live = rest @ constr1.live}
            in
            simplify_left ~succ ~lforms ~saved:((lf, save) :: saved) {constr with live}
          end
      | Shift lf ->
          simplify_left ~lforms ~succ ~saved
            (add_true_constraints [lf] {constr with live})
      | Forall _ | Exists _ | Atom _ -> first_order ()
    end

let create_model res =
  let live = IdtMap.fold begin fun l lf live ->
      match lf.place with
      | Left Global | Left Pseudo -> lf.Form.skel :: live
      | _ -> live
    end res.lforms [] in
  let dead = [] in
  let fals = Some res.goal.skel in
  let constr = {live ; dead ; fals} in
  dprintf "model" "Initial constraint: @[%a@]@." (format_constr res.lforms) constr ;
  simplify_right ~lforms:res.lforms ~succ:(fun m -> m) constr

type simple_model = {
  smid : int ;
  smtrue : IdtSet.t ;
  smkids : simple_model list ;
}

let rec simple_model ~id ~lforms modl =
  let smid = id in
  let smtrue = List.fold_left begin fun smtrue f ->
      match get_atom lforms f with
      | l -> IdtSet.add l smtrue
      | exception Nonatomic -> smtrue
    end IdtSet.empty (modl.constr.live @ modl.constr.dead) in
  let (id, smkids) = List.fold_left begin fun (id, smkids) kid ->
      let (id, smkid) = simple_model ~id ~lforms kid in
      (id, smkid :: smkids)
    end (id + 1, []) modl.kids
  in
  (id, {smid ; smtrue ; smkids})

let simple_model ~lforms modl = snd @@ simple_model ~id:0 ~lforms modl

let rec format_simple_model ff sm =
  let open Format in
  fprintf ff "@[<hv0>w%d |= {%s},@ @[<b1>[%a]@]@]"
    sm.smid
    (String.concat ", " (IdtSet.elements sm.smtrue |> List.map (fun l -> l.rep)))
    format_simple_models sm.smkids

and format_simple_models ff sms =
  match sms with
  | [] -> ()
  | [sm] -> format_simple_model ff sm
  | sm :: sms ->
      format_simple_model ff sm ;
      Format.fprintf ff ",@ " ;
      format_simple_models ff sms

let validate_model res modl =
  let ants = IdtMap.fold begin fun l lf ants ->
      match lf.Form.place with
      | Left Global | Left Pseudo ->
          expand_fully ~lforms:res.lforms lf.Form.skel :: ants
      | _ -> ants
    end res.lforms [] in
  let impl = implies ants (expand_fully ~lforms:res.lforms res.goal.Form.skel) in
  let rec model_check ~ind sm f =
    match f.form with
    | Shift f -> model_check ~ind sm f
    | _ ->
        let indent = String.init (2 * ind) (fun k -> if k mod 2 = 0 then '|' else ' ') in
        let ind = ind + 1 in
        dprintf "modelcheck" "%s(w%d |= %a) ?@." indent sm.smid (format_form ()) f ;
        let ret = match f.form with
          | Atom (_, l, _) ->
              IdtSet.mem l sm.smtrue
          | And (_, f1, f2) ->
              model_check ~ind sm f1 && model_check ~ind sm f2
          | True _ ->
              true
          | Or (f1, f2) ->
              model_check ~ind sm f1 || model_check ~ind sm f2
          | False ->
              false
          | Shift f ->
              assert false
          | Implies (f1, f2) ->
              (model_check ~ind sm f2 ||
               not (model_check ~ind sm f1)) &&
              List.for_all (fun sm -> model_check ~ind sm f) sm.smkids
          | Exists _ | Forall _ ->
              bugf "Cannot model-check first-order formulas"
        in
        dprintf "modelcheck" "%s`-- (w%d |= %a) %b@." indent sm.smid (format_form ()) f ret ;
        ret
  in
  let sm = simple_model ~lforms:res.lforms modl in
  dprintf "modelcheck" "Simplified model: %a@." format_simple_model sm ;
  model_check ~ind:0 sm impl
