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


(******************************************************************************)

type model = {
  assn : IdtSet.t ;
  kids : model list ;
}

type state = {
  left_seen : IdtSet.t ;
  left_passive : IdtSet.t ;
  left_active : form list ;
  right : [`Active of form | `Passive of Idt.t] ;
  right_seen : IdtSet.t ;
}

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

let get_atom_idt lforms l =
  match IdtMap.find l lforms with
  | {Form.skel = {Form.form = Atom (_, l, _); _} ; _} -> l
  | _ -> raise Nonatomic
  | exception Not_found -> l

let rec get_atom lforms f =
  match f.form with
  | Atom (_, l, args) -> get_atom_idt lforms l
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

let pp_indent ff n =
  for i = 1 to n do
    Format.pp_print_string ff "  "
  done

let format_state ff stt =
  let open Format in
  pp_open_box ff 2 ; begin
    let left_passive = List.map begin fun f () ->
        fprintf ff "%s" f.Idt.rep ;
      end (IdtSet.elements stt.left_passive) in
    let left_active =
      if elide_true_nonatoms then [] else
      stt.left_active |>
      List.map begin fun f () ->
        fprintf ff "@[<b1><%a>@]" (format_form ()) f
      end in
    let right ff =
      match stt.right with
      | `Active f ->
          if elide_false_nonatoms then fprintf ff "###" else
          fprintf ff "@[<b1><%a>@]" (format_form ()) f
      | `Passive f ->
          fprintf ff "%s" f.Idt.rep
    in
    IdtSet.pp ff stt.left_seen ;
    fprintf ff ";@ " ;
    (left_passive @ left_active) |>
    List.interleave (fun () -> fprintf ff ",@ ") |>
    List.iter (fun doit -> doit ()) ;
    fprintf ff " -->@ %t ;@ " right ;
    IdtSet.pp ff stt.right_seen ;
  end ; pp_close_box ff ()

let rec format_model_lines indent ff modl =
  let open Format in
  List.iter (format_model_lines (indent + 1) ff) modl.kids ;
  fprintf ff "%a* @[%a@]@," pp_indent indent IdtSet.pp modl.assn

let format_model ff modl =
  Format.fprintf ff "@[<v0>%a@]" (format_model_lines 0) modl

let dot_format_model modl =
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
      w IdtSet.pp modl.assn ;
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

let state_to_model lforms stt =
  let assn = IdtSet.fold begin fun x assn ->
      match get_atom_idt lforms x with
      | x -> IdtSet.add x assn
      | exception Nonatomic -> assn
    end stt.left_passive IdtSet.empty in
  {assn ; kids = []}

let join m1 m2 =  {
  assn = IdtSet.union m1.assn m2.assn ;
  kids = m1.kids @ m2.kids ;
}

let move_forward m = {
  assn = IdtSet.empty ;
  kids = [m] ;
}

let or_models (m1, v1) (m2, v2) =
  if not v1
  then (m1, v1 && v2)
  else (m2, v1 && v2)

(******************************************************************************)

let query stt =
  let get_label l = (l, []) in
  let sq = mk_sequent ()
      ~left:(stt.left_passive |>
             IdtSet.elements |>
             List.map get_label |>
             Ft.of_list)
      ?right:begin
        match stt.right with
        | `Active f -> bugf "query"
        | `Passive l -> Some (get_label l)
      end
  in
  dprintf "modelquery" "Need to check: @[%a@]@." (format_sequent ()) sq ;
  let subs = Inverse.Data.subsumes sq in
  dprintf "modelquery" "Was %ssubsumed@." (if subs then "" else "NOT ") ;
  subs

(******************************************************************************)

let rec right_invert ~ind ~lforms ~succ stt =
  dprintf "model" "%aright_invert: %a@." pp_indent ind format_state stt ;
  let ind = ind + 1 in
  match stt.right with
  | `Passive f -> bugf "right_invert: %s" f.Idt.rep
  | `Active f -> begin
      match f.form with
      | Shift {form = Atom (POS, l, []) ; _}
      | Atom (NEG, l, []) ->
          (if IdtSet.mem l stt.right_seen
           then left_invert ~ind {stt with right = `Passive l}
           else left_invert ~ind {stt with right = `Passive l ; left_seen = IdtSet.empty})
          ~lforms ~succ
      | And (NEG, f1, f2) ->
          (* let ind = ind + 1 in *)
          right_invert ~ind {stt with right = `Active f1}
            ~lforms
            ~succ:(fun mv1 ->
                right_invert ~ind {stt with right = `Active f2}
                  ~lforms
                  ~succ:(fun mv2 ->
                      succ (or_models mv1 mv2)))
      | True NEG ->
          succ (state_to_model lforms stt, true)
      | Implies (f1, f2) ->
          right_invert ~ind {stt with right = `Active f2 ; left_active = f1 :: stt.left_active}
            ~lforms ~succ
      | And (POS, _, _) | True POS | Or _ | False ->
          bugf "right_invert: positive formula %a" (format_form ()) f
      | Shift _ ->
          bugf "right_invert: invalid shift: %a" (format_form ()) f
      | Atom _ | Forall _ | Exists _ -> first_order ()
    end

and left_invert ~ind ~lforms ~succ stt =
  dprintf "model" "%aleft_invert: %a@." pp_indent ind format_state stt ;
  let ind = ind + 1 in
  match stt.left_active with
  | [] -> neutral_right ~ind ~lforms ~succ stt
  | f :: left_active -> begin
      match f.form with
      | Shift {form = Atom (NEG, l, []) ; _}
      | Atom (POS, l, []) ->
          neutral_right ~ind ~lforms ~succ
            (if IdtSet.mem l stt.left_seen
             then (dprintf "model" "Already seen %s@." l.rep ; {stt with left_active})
             else {stt with
                   left_active ;
                   left_passive = IdtSet.add l stt.left_passive ;
                   left_seen = IdtSet.empty ;
                   right_seen = IdtSet.empty})
      | And (POS, f1, f2) ->
          left_invert ~ind {stt with left_active = f1 :: f2 :: left_active}
            ~lforms ~succ
      | True POS ->
          left_invert ~ind {stt with left_active} ~lforms ~succ
      | Or (f1, f2) ->
          (* let ind = ind + 1 in *)
          left_invert ~ind {stt with left_active = f1 :: left_active}
            ~lforms
            ~succ:(fun mv1 ->
                left_invert ~ind {stt with left_active = f2 :: left_active}
                  ~lforms
                  ~succ:(fun mv2 ->
                      succ (or_models mv1 mv2)))
      | False ->
          succ (state_to_model lforms stt, false)
      | And (NEG, _, _) | True NEG | Implies _ ->
          bugf "left_invert: negative formula %a" (format_form ()) f
      | Shift _ ->
          bugf "left_invert: invalid shift: %a" (format_form ()) f
      | Atom _ | Forall _ | Exists _ -> first_order ()
    end

and right_focus ~ind ~lforms ~succ stt =
  dprintf "model" "%aright_focus: %a@." pp_indent ind format_state stt ;
  let ind = ind + 1 in
  match stt.right with
  | `Passive f -> bugf "right_focus: %s" f.Idt.rep
  | `Active f -> begin
      match f.form with
      | Shift f ->
          right_invert ~ind {stt with right = `Active f} ~lforms ~succ
      | Atom (POS, l, []) ->
          succ (state_to_model lforms stt, IdtSet.mem l stt.left_passive)
      | And (POS, f1, f2) ->
          (* let ind = ind + 1 in *)
          right_focus ~ind {stt with right = `Active f1} ~lforms
            ~succ:(fun mv1 ->
                right_focus ~ind {stt with right = `Active f2} ~lforms
                  ~succ:(fun mv2 ->
                      succ (or_models mv1 mv2)))
      | True POS ->
          succ (state_to_model lforms stt, true)
      | Or (f1, f2) ->
          (* let ind = ind + 1 in *)
          right_focus ~ind {stt with right = `Active f1} ~lforms
            ~succ:(fun (m1, v1) ->
                right_focus ~ind {stt with right = `Active f2} ~lforms
                  ~succ:(fun (m2, v2) ->
                      succ (join (move_forward m1) (move_forward m2), v1 || v2)))
      | False ->
          succ (state_to_model lforms stt, false)
      | And (NEG, _, _) | True NEG | Implies _ ->
          bugf "right_focus: negative formula %a" (format_form ()) f
      | Atom _ | Forall _ | Exists _ -> first_order ()
    end

and left_focus ~ind ~lforms ~succ stt =
  dprintf "model" "%aleft_focus: %a@." pp_indent ind format_state stt ;
  let ind = ind + 1 in
  match stt.left_active with
  | [f] -> begin
      match f.form with
      | Shift f ->
          left_invert ~ind {stt with left_active = [f]} ~lforms ~succ
      | Atom (NEG, l, []) ->
          succ (state_to_model lforms stt, stt.right = `Passive l)
      | And (NEG, f1, f2) ->
          (* let ind = ind + 1 in *)
          left_focus ~ind {stt with left_active = [f1]} ~lforms
            ~succ:(fun (m1, v1) ->
                left_focus ~ind {stt with left_active = [f2]} ~lforms
                  ~succ:(fun (m2, v2) ->
                      succ (join m1 m2, v1 || v2)))
      | True NEG ->
          succ (state_to_model lforms stt, false)
      | Implies (f1, f2) ->
          (* let ind = ind + 1 in *)
          right_focus ~ind {stt with left_active = [] ; right = `Active f1} ~lforms
            ~succ:(fun (m1, v1) ->
                left_focus ~ind {stt with left_active = [f2]} ~lforms
                  ~succ:(fun mv2 ->
                      succ (or_models (move_forward m1, v1) mv2)))
      | And (POS, _, _) | True POS | Or _ | False ->
          bugf "left_focus: positive formula %a" (format_form ()) f
      | Atom _ | Forall _ | Exists _ -> first_order ()
    end
  | _ ->
      bugf "left_focus: left active zone not singleton"

and neutral_right ~ind ~lforms ~succ stt =
  dprintf "model" "%aneutral_right: %a@." pp_indent ind format_state stt ;
  let ind = ind + 1 in
  match stt.right with
  | `Active f -> bugf "neutral: right not passive: %a" (format_form ()) f
  | `Passive f -> begin
      if IdtSet.mem f stt.right_seen || query stt then neutral_left ~ind ~lforms ~succ stt else
      let stt = {stt with right_seen = IdtSet.add f stt.right_seen} in
      let f = match IdtMap.find f lforms with
        | lf -> lf.Form.skel
        | exception Not_found -> atom POS f []
      in
      (* let ind = ind + 1 in *)
      neutral_right ~ind stt ~lforms
        ~succ:(fun (m1, v1) ->
            if v1 then succ (m1, v1) else
              right_focus ~ind {stt with right = `Active f} ~lforms
                ~succ:(fun (m2, v2) ->
                    if v2 then succ (m2, v2)
                    else succ (join m1 m2, v2)))
    end

and neutral_left ~ind ~lforms ~succ stt =
  dprintf "model" "%aneutral_left: %a@." pp_indent ind format_state stt ;
  let ind = ind + 1 in
  let rec attempt = function
    | [] ->
        let modl = state_to_model lforms stt in
        let v = query stt in
        dprintf "model" "branch close: sending %b model %a@." v format_model modl ;
        succ (modl, v)
    | f :: fs ->
        if (IdtSet.mem f stt.left_passive || query stt) then attempt fs else
        let stt = {stt with left_seen = IdtSet.add f stt.left_seen} in
        let f = match IdtMap.find f lforms with
          | lf -> lf.Form.skel
          | exception Not_found -> atom NEG f []
        in
        (* let ind = ind + 1 in *)
        neutral_left ~ind stt ~lforms
          ~succ:(fun (m1, v1) ->
              if v1 then succ (m1, v1) else
                left_focus ~ind {stt with left_active = [f]} ~lforms
                  ~succ:(fun (m2, v2) ->
                      if v2 then succ (m2, v2)
                      else succ (join m1 m2, v2)))
  in
  attempt (IdtSet.elements stt.left_passive)

(******************************************************************************)

type lmodel = {
  id : int ;
  lassn : IdtSet.t ;
  lkids : lmodel list ;
}

let rec label_model id0 modl =
  let lkids, id = label_models (id0 + 1) modl.kids in
  ({id = id0 ; lassn = modl.assn ; lkids}, id)

and label_models id0 ms =
  match ms with
  | [] -> ([], id0)
  | m :: ms ->
      let (m, id) = label_model id0 m in
      let (ms, id) = label_models id ms in
      (m :: ms, id)

let label_model modl = fst (label_model 0 modl)

let rec format_lmodel ff sm =
  let open Format in
  fprintf ff "@[<hv0>w%d |= {%a},@ @[<b1>[%a]@]@]"
    sm.id
    IdtSet.pp sm.lassn
    format_lmodels sm.lkids

and format_lmodels ff sms =
  match sms with
  | [] -> ()
  | [sm] -> format_lmodel ff sm
  | sm :: sms ->
      format_lmodel ff sm ;
      Format.fprintf ff ",@ " ;
      format_lmodels ff sms

let validate_model res modl =
  let sm = label_model modl in
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
        dprintf "modelcheck" "%s(w%d |= %a) ?@." indent sm.id (format_form ()) f ;
        let ret = match f.form with
          | Atom (_, l, _) ->
              IdtSet.mem l sm.lassn
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
              List.for_all (fun sm -> model_check ~ind sm f) sm.lkids
          | Exists _ | Forall _ ->
              bugf "Cannot model-check first-order formulas"
        in
        dprintf "modelcheck" "%s`-- (w%d |= %a) %b@." indent sm.id (format_form ()) f ret ;
        ret
  in
  dprintf "modelcheck" "Simplified model: %a@." format_lmodel sm ;
  model_check ~ind:0 sm impl

(*****************************************************************************)

let create_model res =
  let left_passive = IdtMap.fold begin fun l lf live ->
      match lf.place with
      | Left Global | Left Pseudo -> IdtSet.add lf.Form.label live
      | _ -> live
    end res.lforms IdtSet.empty in
  let stt = {
    left_seen = IdtSet.empty ;
    left_passive ;
    left_active = [] ;
    right = `Passive res.goal.label ;
    right_seen = IdtSet.empty ;
  } in
  dprintf "model" "Initial constraint: @[%a@]@." format_state stt ;
  neutral_right ~ind:0 stt
    ~lforms:res.lforms
    ~succ:(fun mv -> mv)
