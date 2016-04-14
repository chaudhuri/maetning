(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2016  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

let paranoid             = false
let compress_model       = true
let memoize              = true
let rewrite              = true
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
  left_dead : IdtSet.t ;
  left_active : form list ;
  right_seen : IdtSet.t ;
  right : [`Active of form | `Passive of Idt.t | `Dead of Idt.t] ;
}

let false_atom = Idt.intern "#<FALSE>"

exception Model

let first_order f =
  Format.eprintf "Cannot construct countermodels for first-order formulas@.%a@." (format_form ()) f ;
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
    | Forall _ | Exists _ | Atom _ -> first_order f
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

let format_state annot ff stt =
  let open Format in
  pp_open_box ff 2 ; begin
    let left_passive = List.map begin fun f () ->
        fprintf ff "%s" f.Idt.rep ;
      end (IdtSet.elements stt.left_passive) in
    let left_dead = List.map begin fun f () ->
        fprintf ff "%s⁺" f.Idt.rep ;
      end (IdtSet.elements stt.left_dead) in
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
      | `Dead f ->
          fprintf ff "%s⁻" f.Idt.rep
    in
    IdtSet.pp ff stt.left_seen ;
    fprintf ff " ;@ " ;
    (left_passive @ left_dead @ left_active) |>
    List.interleave (fun () -> fprintf ff ",@ ") |>
    List.iter (fun doit -> doit ()) ;
    fprintf ff " -%s->@ %t ;@ " annot right ;
    IdtSet.pp ff stt.right_seen
  end ; pp_close_box ff ()

let rec format_model ff modl =
  let open Format in
  if IdtSet.is_empty modl.assn && modl.kids = [] then fprintf ff "∅" else
  let assn =
    IdtSet.elements modl.assn |>
    List.map (fun f () -> fprintf ff "%s" f.rep)
  in
  let kids =
    modl.kids |>
    List.map (fun modl () -> fprintf ff "@[<b1>{%a}@]" format_model modl)
  in
  (assn @ kids) |>
  List.interleave (fun () -> fprintf ff ",@ ") |>
  List.iter (fun doit -> doit ())

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
  let add_atoms_from set assn =
    IdtSet.fold begin fun x assn ->
      match get_atom_idt lforms x with
      | x -> IdtSet.add x assn
      | exception Nonatomic -> assn
    end set assn
  in
  let assn = add_atoms_from stt.left_seen IdtSet.empty in
  let assn = add_atoms_from stt.left_passive assn in
  let assn = add_atoms_from stt.left_dead assn in
  {assn ; kids = []}

let rec percolate assn modl =
  if IdtSet.subset assn modl.assn then modl else
  let assn = IdtSet.union assn modl.assn in
  {assn ; kids = List.map (percolate assn) modl.kids}

let join m1 m2 =
  let assn = IdtSet.union m1.assn m2.assn in
  {assn ; kids = List.map (percolate assn) (m1.kids @ m2.kids)}

let move_forward m =
  {assn = IdtSet.empty ; kids = [m]}

let empty_model = {assn = IdtSet.empty ; kids = []}

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

let validate_state lforms stt modl =
  let sm = label_model modl in
  let ants = List.map (expand_fully ~lforms) stt.left_active in
  let ants = IdtSet.fold begin fun l ants ->
      expand_fully ~lforms (atom NEG l []) :: ants
    end (IdtSet.diff stt.left_passive stt.left_seen) ants in
  let ants = IdtSet.fold begin fun l ants ->
      (atom POS l []) :: ants
    end stt.left_dead ants in
  let concl = match stt.right with
    | `Active f ->
        expand_fully ~lforms f
    | `Dead f ->
        if IdtSet.mem f stt.right_seen then
          atom NEG false_atom []
        else
          atom NEG f []
    | `Passive f ->
        if IdtSet.mem f stt.right_seen then
          atom POS false_atom []
        else
          expand_fully ~lforms (atom POS f [])
  in
  let impl = implies ants concl in
  (impl, model_check ~ind:0 sm impl)

let validate_model res modl =
  let sm = label_model modl in
  let ants = IdtMap.fold begin fun l lf ants ->
      match lf.Form.place with
      | Left Global | Left Pseudo ->
          expand_fully ~lforms:res.lforms lf.Form.skel :: ants
      | _ -> ants
    end res.lforms [] in
  let impl = implies ants (expand_fully ~lforms:res.lforms res.goal.Form.skel) in
  dprintf "modelcheck" "Simplified model: %a@." format_lmodel sm ;
  model_check ~ind:0 sm impl

(******************************************************************************)

let query stt =
  let get_label l = (l, []) in
  let sq = mk_sequent ()
      ~left:((IdtSet.union stt.left_seen (IdtSet.union stt.left_passive stt.left_dead)) |>
             IdtSet.elements |>
             List.map get_label |>
             Ft.of_list)
      ?right:begin
        match stt.right with
        | `Active f -> bugf "query"
        | `Passive l -> Some (get_label l)
        | `Dead l -> Some (l, [])
      end
  in
  dprintf "modelquery" "Need to check: @[%a@]@." (format_sequent ()) sq ;
  let subs = Inverse.Data.subsumes sq in
  dprintf "modelquery" "Was %ssubsumed@." (if subs then "" else "NOT ") ;
  subs

(******************************************************************************)

let rec check_monotone modl =
  IdtSet.for_all begin fun x ->
    List.for_all (is_assigned x) modl.kids
  end modl.assn

and is_assigned x modl =
  IdtSet.mem x modl.assn &&
  List.for_all (is_assigned x) modl.kids

let pp_indent ff n =
  for i = 1 to n do
    Format.pp_print_as ff 2 "│ "
  done

type meval =
  | Valid
  | Counter of model

let forward_meval mv =
  match mv with
  | Valid -> Valid
  | Counter m -> Counter (move_forward m)

let format_meval ff mv =
  match mv with
  | Valid -> Format.pp_print_string ff "true"
  | Counter m -> Format.fprintf ff "@[<h>false: %a@]" format_model m

let memo : (state * string, meval) Hashtbl.t = Hashtbl.create 19
let reset_memo () = Hashtbl.clear memo

let record ~ind ~lforms innerfn desc annot stt =
  dprintf "model" "%s:@.@[<h>%a %a@]@." desc pp_indent ind (format_state annot) stt ;
  dprintf "modelstate" "@[<h>%a@]@." (format_state "") stt ;
  let mv =
    if not memoize then innerfn ~ind ~lforms stt else
    match Hashtbl.find memo (stt, annot) with
    | mv ->
        dprintf "modelstate" "SEEN@." ;
        mv
    | exception Not_found ->
        let mv = innerfn ~ind ~lforms stt in
        Hashtbl.replace memo (stt, annot) mv ;
        mv
  in
  dprintf "model" "%s:@.@[<h>%a@<3>%s %a@]@." desc pp_indent ind "└──" format_meval mv ;
  dprintf "model" "%s:@.@[<h>%a    for %a@]@." desc pp_indent ind (format_state annot) stt ;
  if paranoid then begin
    match mv with
    | Counter modl when List.mem annot ["nr" ; "nl"] ->
        dprintf "model" "@.@[<h>%a    paranoid checking %a |= %a@]@."
          pp_indent ind
          format_model modl
          (format_state annot) stt ;
        let (impl, eval) = validate_state lforms stt modl in
        if eval then
          bugf "paranoid mode found satisfying model:@.@[<h>%a |= %a@]@."
            format_model modl
            (format_form ()) impl ;
    | _ -> ()
  end ;
  mv

let rec make_true l f =
  match f.form with
  | Atom (pol, pl, []) ->
      if pl = l then conj ~pol [] else f
  | And (pol, f1, f2) -> begin
      let f1 = make_true l f1 in
      match f1.form with
      | True _ -> make_true l f2
      | _ -> conj ~pol [f1 ; make_true l f2]
    end
  | Or (f1, f2) -> begin
      let f1 = make_true l f1 in
      match f1.form with
      | True _ -> f1
      | _ -> begin
          let f2 = make_true l f2 in
          match f2.form with
          | True _ -> f2
          | _ -> disj [f1 ; f2]
        end
    end
  | Implies (f1, f2) -> begin
      let f1 = make_true l f1 in
      match f1.form with
      | True _ -> make_true l f2
      | _ -> begin
          let f2 = make_true l f2 in
          match f2.form with
          | True _ -> conj ~pol:NEG []
          | _ -> implies [f1] f2
        end
    end
  | Shift f -> begin
      let f = make_true l f in
      match f.form with
      | True pol -> conj ~pol:(dual_polarity pol) []
      | _ -> shift f
    end
  | Atom _ | True _ | False | Forall _ | Exists _ -> f

let rec make_true_lform l lf =
  let new_skel = make_true l lf.Form.skel in
  if lf.Form.skel = new_skel then lf else begin
    dprintf "modelsimplify" "@[<h>Simplified %s from %a to %a@]@."
      lf.label.rep (format_form ()) lf.Form.skel (format_form ()) new_skel ;
    {lf with Form.skel = new_skel}
  end

let rec right_invert ishere ~ind ~lforms stt =
  record (right_invert_inner ishere) "right_invert" "ri" stt ~ind ~lforms

and right_invert_inner ishere ~ind ~lforms stt =
  let ind = ind + 1 in
  match stt.right with
  | `Passive f | `Dead f -> bugf "right_invert: %s" f.Idt.rep
  | `Active f -> begin
      match f.form with
      | Shift {form = Atom (POS, l, []) ; _} ->
          let stt = {stt with right = `Passive l} in
          let stt =
            if IdtSet.mem l stt.right_seen then stt else
              {stt with
               left_passive = IdtSet.union stt.left_seen stt.left_passive ;
               left_seen = IdtSet.empty(*  ; *)
               (* right_seen = IdtSet.add l stt.right_seen *)}
          in
          left_invert stt ~ind ~lforms
      | Atom (NEG, l, []) ->
          let stt = {stt with right = `Dead l} in
          let stt =
            if IdtSet.mem l stt.right_seen then stt else
              {stt with
               left_passive = IdtSet.union stt.left_seen stt.left_passive ;
               left_seen = IdtSet.empty ;
               right_seen = IdtSet.add l stt.right_seen}
          in
          left_invert stt ~ind ~lforms
      | And (NEG, f1, f2) -> begin
          match right_invert ishere {stt with right = `Active f1} ~ind ~lforms with
          | Valid ->
              right_invert ishere {stt with right = `Active f2} ~ind ~lforms
          | Counter _ as mv1 -> mv1
        end
      | True NEG ->
          Valid
      | Implies (f1, f2) -> begin
          let mv = right_invert false {stt with right = `Active f2 ; left_active = f1 :: stt.left_active}
              ~ind ~lforms in
          if ishere then forward_meval mv else mv
(* [RIGHT IMPLIES]
          match right_invert {stt with right = `Active f2 ; left_active = f1 :: stt.left_active}
                  ~ind ~lforms with
          | Valid -> Valid
          | Counter m1 -> begin
              match right_invert {stt with right = `Active f2} ~ind ~lforms with
              | Valid -> Valid
              | Counter m2 ->
                  Counter (join m1 m2)
            end
*)
        end

      | Atom (POS, _, _) | And (POS, _, _) | True POS | Or _ | False ->
          bugf "right_invert: positive formula %a" (format_form ()) f
      | Shift _ ->
          bugf "right_invert: invalid shift: %a" (format_form ()) f
      | Atom _ | Forall _ | Exists _ -> first_order f
    end

and left_invert ~ind ~lforms stt =
  record left_invert_inner "left_invert" "li" stt ~ind ~lforms

and left_invert_inner ~ind ~lforms stt =
  let ind = ind + 1 in
  match stt.left_active with
  | [] ->
      neutral_right ~ind ~lforms stt
  | f :: left_active -> begin
      match f.form with
      | Shift {form = Atom (NEG, l, []) ; _} ->
          let seen = IdtSet.mem l stt.left_passive || IdtSet.mem l stt.left_seen in
          let stt = if seen then {stt with left_active} else
              {stt with
               left_active ;
               left_passive = IdtSet.union stt.left_seen (IdtSet.add l stt.left_passive) ;
               left_seen = IdtSet.empty ;
               right_seen = IdtSet.empty}
          in
          let lforms = if not rewrite || seen then lforms else IdtMap.map (make_true_lform l) lforms in
          left_invert stt ~ind ~lforms
      | Atom (POS, l, []) ->
          let seen = IdtSet.mem l stt.left_dead in
          let stt = if seen then {stt with left_active} else
              {stt with
               left_active ;
               left_passive = IdtSet.union stt.left_seen stt.left_passive ;
               left_dead = IdtSet.add l stt.left_dead ;
               left_seen = IdtSet.empty ;
               right_seen = IdtSet.empty}
          in
          let lforms = if not rewrite || seen then lforms else IdtMap.map (make_true_lform l) lforms in
          left_invert stt ~ind ~lforms
      | And (POS, f1, f2) ->
          left_invert {stt with left_active = f1 :: f2 :: left_active}
            ~ind ~lforms
      | True POS ->
          left_invert {stt with left_active} ~ind ~lforms
      | Or (f1, f2) -> begin
          match left_invert {stt with left_active = f1 :: left_active} ~ind ~lforms with
          | Valid ->
              left_invert {stt with left_active = f2 :: left_active} ~ind ~lforms
          | Counter _ as mv1 -> mv1
        end
      | False ->
          Valid
      | Atom (NEG, _, _) | And (NEG, _, _) | True NEG | Implies _ ->
          bugf "left_invert: negative formula %a" (format_form ()) f
      | Shift _ ->
          bugf "left_invert: invalid shift: %a" (format_form ()) f
      | Atom _ | Forall _ | Exists _ -> first_order f
    end

and right_focus ~ind ~lforms stt =
  record right_focus_inner "right_focus" "rf" stt ~ind ~lforms

and right_focus_inner ~ind ~lforms stt =
  let ind = ind + 1 in
  match stt.right with
  | `Passive f | `Dead f -> bugf "right_focus: %s" f.Idt.rep
  | `Active f -> begin
      match f.form with
      | Shift f ->
          right_invert true {stt with right = `Active f} ~ind ~lforms
      | Atom (POS, l, []) ->
          if IdtSet.mem l stt.left_dead then Valid
          else Counter empty_model
          (* let stt = *)
          (*   if IdtSet.mem l stt.right_seen then {stt with right = `Passive l} else *)
          (*     {stt with *)
          (*      left_seen = IdtSet.empty ; *)
          (*      left_passive = IdtSet.union stt.left_seen stt.left_passive ; *)
          (*      right = `Passive l ; *)
          (*      right_seen = IdtSet.add l stt.right_seen} *)
          (* in *)
          (* neutral_left stt ~ind ~lforms |> forward_meval *)
      | And (POS, f1, f2) -> begin
          match right_focus {stt with right = `Active f1} ~ind ~lforms with
          | Valid -> right_focus {stt with right = `Active f2} ~ind ~lforms
          | Counter _ as mv1 -> mv1
        end
      | True POS ->
          Valid
      | Or (f1, f2) -> begin
          (* let ind = ind + 1 in *)
          match right_focus {stt with right = `Active f1} ~ind ~lforms (* |> forward_meval *) with
          | Valid -> Valid
          | Counter m1 -> begin
              match right_focus {stt with right = `Active f2} ~ind ~lforms (* |> forward_meval *) with
              | Valid -> Valid
              | Counter m2 ->
                  Counter (join m1 m2)
            end
        end
      | False ->
          let stt = {stt with
                     left_seen = IdtSet.empty ;
                     left_passive = IdtSet.union stt.left_seen stt.left_passive ;
                     right = `Passive false_atom ;
                     right_seen = IdtSet.add false_atom stt.right_seen} in
          neutral_left stt ~ind ~lforms
      | Atom (NEG, _, _) | And (NEG, _, _) | True NEG | Implies _ ->
          bugf "right_focus: negative formula %a" (format_form ()) f
      | Atom _ | Forall _ | Exists _ -> first_order f
    end

and left_focus ~ind ~lforms stt =
  record left_focus_inner "left_focus" "lf" stt ~ind ~lforms

and left_focus_inner ~ind ~lforms stt =
  let ind = ind + 1 in
  match stt.left_active with
  | [f] -> begin
      match f.form with
      | Shift f ->
          left_invert ~ind {stt with left_active = [f]} ~lforms
      | Atom (NEG, l, []) ->
          if stt.right = `Dead l then Valid
          else Counter {assn = IdtSet.singleton l ; kids = []}
          (* let stt = {stt with *)
          (*            left_active = [] ; *)
          (*            left_passive = IdtSet.add l stt.left_passive ; *)
          (*            left_seen = IdtSet.add l stt.left_seen} in *)
          (* neutral_right stt ~ind ~lforms *)
      | And (NEG, f1, f2) -> begin
          (* let ind = ind + 1 in *)
          match left_focus {stt with left_active = [f1]} ~ind ~lforms with
          | Valid ->
              left_focus {stt with left_active = [f2]} ~ind ~lforms
          | Counter m1 -> begin
              match left_focus {stt with left_active = [f2]} ~ind ~lforms with
              | Valid -> Valid
              | Counter m2 ->
                  Counter (join m1 m2)
            end
        end
      | True NEG ->
          Counter empty_model (* (state_to_model lforms stt) *)
      | Implies (f1, f2) -> begin
          (* match left_focus {stt with left_active = [f2]} ~ind ~lforms with *)
          (* | Valid -> *)
          (*     right_focus {stt with left_active = [] ; right = `Active f1} ~ind ~lforms (\* |> forward_meval *\) *)
          (* | Counter _ as mv2 -> mv2 *)
          match right_focus {stt with left_active = [] ; right = `Active f1} ~ind ~lforms |> forward_meval with
          | Valid ->
              left_focus {stt with left_active = [f2]} ~ind ~lforms
          | Counter _ as mv1 -> mv1
        end
      | Atom (POS, _, _) | And (POS, _, _) | True POS | Or _ | False ->
          bugf "left_focus: positive formula %a" (format_form ()) f
      | Atom _ | Forall _ | Exists _ -> first_order f
    end
  | _ ->
      bugf "left_focus: left active zone not singleton"

and neutral_right ~ind ~lforms stt =
  record neutral_right_inner "neutral_right" "nr" stt ~ind ~lforms

and neutral_right_inner ~ind ~lforms stt =
  let ind = ind + 1 in
  match stt.right with
  | `Active f -> bugf "neutral: right not passive: %a" (format_form ()) f
  | `Dead f ->
      neutral_left ~ind ~lforms stt
  | `Passive l -> begin
      if IdtSet.mem l stt.right_seen || query stt then neutral_left ~ind ~lforms stt else
      let f = match IdtMap.find l lforms with
        | lf -> lf.Form.skel
        | exception Not_found -> atom POS l []
      in
      (* let ind = ind + 1 in *)
      match f.form with
      | Shift {form = False ; _} ->
          neutral_left {stt with right = `Dead false_atom ; right_seen = IdtSet.add false_atom stt.right_seen}
            ~ind ~lforms
      | _ -> begin
          let stt = {stt with right_seen = IdtSet.add l stt.right_seen} in
          match neutral_left stt ~ind ~lforms with
          | Valid -> Valid
          | Counter m1 -> begin
              match right_focus {stt with right = `Active f} ~ind ~lforms with
              | Valid -> Valid
              | Counter m2 -> Counter (join m1 m2)
            end
        end
    end

and neutral_left ~ind ~lforms stt =
  record neutral_left_inner "neutral_left" "nl" stt ~ind ~lforms

and neutral_left_inner ~ind ~lforms stt =
  let ind = ind + 1 in
  match IdtSet.pop stt.left_passive with
  | exception Not_found ->
      if query stt then Valid else
      let modl = state_to_model lforms stt in
      Counter modl
  | f, left_passive ->
      let stt = {stt with left_passive ; left_seen = IdtSet.add f stt.left_seen} in
      let f = match IdtMap.find f lforms with
        | lf -> lf.Form.skel
        | exception Not_found -> atom NEG f []
      in
      match neutral_left stt ~ind ~lforms with
      | Valid -> Valid
      | Counter m1 -> begin
          match left_focus {stt with left_active = [f]} ~ind ~lforms with
          | Valid -> Valid
          | Counter m2 ->
              Counter (join m1 m2)
        end

(*****************************************************************************)

let rec eq_models m1 m2 =
  IdtSet.equal m1.assn m2.assn &&
  List.length m1.kids = List.length m2.kids &&
  List.for_all2 eq_models m1.kids m2.kids

let rec compress modl =
  let kids = modl.kids |>
             List.map compress |>
             List.sort (fun m1 m2 -> IdtSet.compare m1.assn m2.assn) |>
             List.unique ~eq:eq_models in
  match kids with
  | [kid] when IdtSet.equal modl.assn kid.assn -> kid
  | _ -> {modl with kids}

let compress_meval = function
  | Valid -> Valid
  | Counter modl -> Counter (compress modl)

let create_model res =
  reset_memo () ;
  let left_passive = IdtMap.fold begin fun l lf live ->
      match lf.place with
      | Left Global | Left Pseudo -> IdtSet.add lf.Form.label live
      | _ -> live
    end res.lforms IdtSet.empty in
  let stt = {
    left_seen = IdtSet.empty ;
    left_passive ;
    left_dead = IdtSet.empty ;
    left_active = [] ;
    right_seen = IdtSet.empty ;
    right = `Passive res.goal.label ;
  } in
  dprintf "model" "Initial constraint: @[%a@]@." (format_state "nr") stt ;
  let mv = neutral_right stt ~ind:0 ~lforms:res.lforms in
  dprintf "model" "Created:@.@[%a@]@." format_meval mv ;
  if compress_model then compress_meval mv else mv
