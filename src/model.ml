(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2016  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

let compress_model       = true

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

let empty_model = {assn = IdtSet.empty ; kids = []}

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

type meval =
  | Valid
  | Counter of model

let cross mu1 mu2 =
  match mu1 () with
  | Valid -> Valid
  | Counter m1 -> begin
      match mu2 () with
      | Valid -> Valid
      | Counter m2 ->
          Counter {
            assn = IdtSet.union m1.assn m2.assn ;
            kids = m1.kids @ m2.kids ;
          }
    end

let forward = function
  | Valid -> Valid
  | Counter modl -> Counter {assn = IdtSet.empty ; kids = [modl]}

(******************************************************************************)

exception Model

let first_order f =
  Format.eprintf "Cannot construct countermodels for first-order formulas@.%a@." format_form f ;
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
  format_form ff (expand f)

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

(******************************************************************************)
(* Model checking *)

module Check : sig
  val check : ind:int -> model -> form -> bool
  val validate : 'a result -> model -> bool
end = struct
  type lmodel = {
    id : int ;
    lassn : IdtSet.t ;
    lkids : lmodel list ;
  }

  let rec label_model id0 modl =
    let (lkids, id) = label_models (id0 + 1) modl.kids in
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

  let rec lcheck ~ind sm f =
    match f.form with
    | Shift f -> lcheck ~ind sm f
    | _ ->
        let indent = String.init (2 * ind) (fun k -> if k mod 2 = 0 then '|' else ' ') in
        let ind = ind + 1 in
        dprintf "modelcheck" "%s(w%d |= %a) ?@." indent sm.id format_form f ;
        let ret = match f.form with
          | Atom (_, l, _) ->
              IdtSet.mem l sm.lassn
          | And (_, f1, f2) ->
              lcheck ~ind sm f1 && lcheck ~ind sm f2
          | True _ ->
              true
          | Or (f1, f2) ->
              lcheck ~ind sm f1 || lcheck ~ind sm f2
          | False ->
              false
          | Shift f ->
              assert false
          | Implies (f1, f2) ->
              (lcheck ~ind sm f2 ||
               not (lcheck ~ind sm f1)) &&
              List.for_all (fun sm -> lcheck ~ind sm f) sm.lkids
          | Exists _ | Forall _ ->
              bugf "Cannot model-check first-order formulas"
        in
        dprintf "modelcheck" "%s`-- (w%d |= %a) %b@." indent sm.id format_form f ret ;
        ret

  let check ~ind modl f = lcheck ~ind (label_model modl) f

  let validate res modl =
    let sm = label_model modl in
    let ants = IdtMap.fold begin fun l lf ants ->
        match lf.Form.place with
        | Left Global | Left Pseudo ->
            expand_fully ~lforms:res.lforms lf.Form.skel :: ants
        | _ -> ants
      end res.lforms [] in
    let impl = implies ants (expand_fully ~lforms:res.lforms res.goal.Form.skel) in
    dprintf "modelcheck" "Simplified model: %a@." format_lmodel sm ;
    lcheck ~ind:0 sm impl
end

(******************************************************************************)
(* Model building *)

module Build : sig val build : 'a result -> meval end = struct
  let propify l = (l, [])

  type extend_result =
    | Seen
    | Subsumed
    | New of IdtSet.t

  let maximally_extend ~lforms ~left ~right ls =
    let left0 = left in
    let left = IdtSet.union left ls in
    let sq0 = mk_sequent ()
        ~left:(IdtSet.elements left |>
               List.map propify |>
               Ft.of_list)
        ?right:(Option.map propify right)
    in
    if Inverse.Data.subsumes ~all:true sq0 then Subsumed else
    let maybe_extend l (left, sq) =
      if IdtSet.mem l left then (left, sq) else
      let new_sq = override sq ~left:(Ft.snoc sq.Sequent.left (propify l)) in
      if Inverse.Data.subsumes ~all:true new_sq then begin
        (* Format.eprintf "SUBSUMED: %a@." (format_sequent ()) new_sq ; *)
        (left, sq)
      end else begin
        (* Format.eprintf  "NEW: %a@." (format_sequent ()) new_sq ; *)
        (IdtSet.add l left, new_sq)
      end
    in
    let (left, _sq) = IdtMap.fold begin fun _ lf (left, sq) ->
        match lf.Form.place with
        | Left _ ->
            maybe_extend lf.Form.label (left, sq)
        | Right -> (left, sq)
      end lforms (left, sq0) in
    (* Format.eprintf "Extended\n  %a\ninto\n  %a@." (format_sequent ()) sq0 (format_sequent ())sq ; *)
    if IdtSet.equal left left0 then Seen else New left

  let __indent = ref 0
  let with_indent fn =
    let old_indent = !__indent in
    incr __indent ;
    match fn (String.make old_indent '|') with
    | exception e ->
        decr __indent ; raise e
    | res ->
        decr __indent ; res

  let format_meval ff mu =
    match mu with
    | Valid -> Format.pp_print_string ff "*"
    | Counter modl -> format_model ff modl

  let __dot = Idt.intern "."

  let format_right ff right =
    match right with
    | None -> Format.pp_print_string ff "."
    | Some l -> Format.pp_print_string ff l.rep

  let rec format_forms ff fs =
    match fs with
    | [] -> ()
    | [f] -> format_form ff f
    | f :: fs ->
        format_form ff f ;
        Format.pp_print_string ff "," ;
        Format.pp_print_space ff () ;
        format_forms ff fs

  type state = {
    left : IdtSet.t ;
    right : Idt.t option ;
    old_rights : IdtSet.t ;
  }

  let rec decision ~lforms ~state =
    let format_state ff =
      Format.fprintf ff "@[%a@ |- %a@ / %a@]"
        IdtSet.pp state.left
        format_right state.right
        IdtSet.pp state.old_rights
    in
    with_indent begin fun ind ->
      dprintf ~ind "modelbuild" "--> decision: %t@." format_state ;
      let mu = decision_ ~lforms ~state in
      dprintf ~ind "modelbuild" "<-- decision: @[%a@]@." format_meval mu ;
      mu
    end

  and decision_ ~lforms ~state =
    let modl = Counter empty_model in
    let modl = IdtSet.fold begin fun idt modl ->
        let f =
          try (IdtMap.find idt lforms).Form.skel with
          | Not_found -> atom NEG idt []
        in
        (* if polarity f = POS then modl else *)
        cross (fun () -> modl) (fun () -> focus_left ~lforms ~state f)
    end state.left modl in
    let modl = match state.right with
      | None -> modl
      | Some idt -> begin
          match (IdtMap.find idt lforms).Form.skel with
          | f -> cross (fun () -> modl) (fun () -> focus_right ~lforms ~state f)
          | exception Not_found -> modl
        end
    in
    modl

  and focus_left ~lforms ~state f =
    let format_state ff =
      Format.fprintf ff "@[%a ; [%a]@ |- %a@ / %a@]"
        IdtSet.pp state.left
        format_form f
        format_right state.right
        IdtSet.pp state.old_rights
    in
    with_indent begin fun ind ->
      dprintf ~ind "modelbuild" "--> focus_left: %t@."
        format_state ;
      let mu = focus_left_ ~lforms ~state f in
      dprintf ~ind "modelbuild" "<-- focus_left: @[%a@]@." format_meval mu ;
      mu
    end

  and focus_left_ ~lforms ~state f =
    match f.Form.form with
    | Shift f ->
        invert_left ~lforms ~state [f]
    | Atom (NEG, l, []) -> begin
        match state.right with
        | Some ll when l = ll ->
            Valid
        | _ ->
            Counter {
              assn = IdtSet.singleton l ;
              kids = [] ;
            }
      end
    | Atom (POS, l, []) ->
        Counter {
          assn = IdtSet.singleton l ;
          kids = [] ;
        }
    | And (NEG, f1, f2) ->
        cross
          (fun () -> focus_left ~lforms ~state f1)
          (fun () -> focus_left ~lforms ~state f2)
    | True NEG ->
        Counter empty_model
    | Implies (f1, f2) -> begin
        (* [ORDERING] Doing it in antecedent-first order is necessary for soundness *)
        (* match focus_left ~lforms ~state f2 with *)
        (* | Valid -> *)
        (*     focus_right ~lforms ~state f1 *)
        (* | Counter _ as mu -> mu *)
        match focus_right ~lforms ~state f1 with
        | Valid ->
            focus_left ~lforms ~state f2
        | Counter _ as mu -> mu
      end
    | And (POS, _, _) | True POS | Or _ | False ->
        bugf "focus_left: positive formula %a" format_form f
    | Atom _ | Forall _ | Exists _ -> first_order f

  and focus_right ~lforms ~state f =
    let format_state ff =
      Format.fprintf ff "@[%a@ |- [%a]@ / %a@]"
        IdtSet.pp state.left
        format_form f
        IdtSet.pp state.old_rights
    in
    with_indent begin fun ind ->
      dprintf ~ind "modelbuild" "--> focus_right: %t@."
        format_state ;
      let mu = focus_right_ ~lforms ~state f in
      dprintf ~ind "modelbuild" "<-- focus_right: @[%a@]@." format_meval mu ;
      mu
    end

  and focus_right_ ~lforms ~state f =
    match f.Form.form with
    | Shift f ->
        invert_right ~lforms ~state f
    | Atom (POS, l, []) ->
        if IdtSet.mem l state.left then Valid else Counter empty_model
    | And (POS, f1, f2) -> begin
        match focus_right ~lforms ~state f1 with
        | Valid -> focus_right ~lforms ~state f2
        | Counter _ as mu -> mu
      end
    | True POS ->
        Valid
    | Or (f1, f2) ->
        cross
          (fun () -> focus_right ~lforms ~state f1)
          (fun () -> focus_right ~lforms ~state f2)
    | False ->
        Counter empty_model
    | Atom (NEG, _, _) | And (NEG, _, _) | True NEG | Implies _ ->
        bugf "focus_right: negative formula %a" format_form f
    | Atom _ | Forall _ | Exists _ -> first_order f

  and invert_left ~lforms ~state ?store fs =
    let format_state ff =
      Format.fprintf ff "@[%a ;@ %a ;@ %a @ |- %a@ / %a@]"
        IdtSet.pp state.left
        IdtSet.pp (Option.default IdtSet.empty store)
        format_forms fs
        format_right state.right
        IdtSet.pp state.old_rights
    in
    with_indent begin fun ind ->
      dprintf ~ind "modelbuild" "--> invert_left: %t@."
        format_state ;
      let mu = invert_left_ ~lforms ~state ?store fs in
      dprintf ~ind "modelbuild" "<-- invert_left: @[%a@]@." format_meval mu ;
      mu
    end

  and invert_left_ ~lforms ~state ?(store=IdtSet.empty) fs =
    match fs with
    | [] -> begin
        match maximally_extend ~lforms ~left:state.left ~right:state.right store with
        | Seen -> begin
            (* dprintf "modelbuild" "maximal_extend: seen@." ; *)
            let is_repeat = match state.right with
              | Some r -> IdtSet.mem r state.old_rights
              | None -> false
            in
            if is_repeat then Counter empty_model else
            let state = match state.right with
              | Some l -> {state with old_rights = IdtSet.add l state.old_rights}
              | None -> state
            in
            decision ~lforms ~state
          end
        | Subsumed ->
            dprintf "modelbuild" "maximal_extend: subsumed@." ;
            Valid
        | New left ->
            (* dprintf "modelbuild" "maximal_extend: new@." ; *)
            let state = {state with left ; old_rights = IdtSet.empty} in
            let state = match state.right with
              | Some l -> {state with old_rights = IdtSet.add l state.old_rights}
              | None -> state
            in
            forward (decision ~lforms ~state)
      end
    | f :: fs -> begin
        match f.Form.form with
        | Atom (POS, l, [])
        | Shift {form = Atom (NEG, l, []) ; _} ->
            invert_left ~lforms ~state ~store:(IdtSet.add l store) fs
        | And (POS, f1, f2) ->
            invert_left ~lforms ~state ~store (f1 :: f2 :: fs)
        | True POS ->
            invert_left ~lforms ~state ~store fs
        | Or (f1, f2) -> begin
            match invert_left ~lforms ~state ~store (f1 :: fs) with
            | Valid ->
                invert_left ~lforms ~state ~store (f2 :: fs)
            | Counter _ as mu -> mu
          end
        | False ->
            Valid
        | Atom (NEG, _, _) | And (NEG, _, _) | True NEG | Implies _ ->
            bugf "invert_left: negative formula %a" format_form f
        | Shift _ ->
            bugf "invert_left: invalid shift: %a" format_form f
        | Atom _ | Forall _ | Exists _ -> first_order f
      end

  and invert_right ~lforms ~state ?lact f =
    let format_state ff =
      Format.fprintf ff "@[%a ;@ %a@ |- %a@ / %a@]"
        IdtSet.pp state.left
        format_forms (Option.default [] lact)
        format_form f
        IdtSet.pp state.old_rights
    in
    with_indent begin fun ind ->
      dprintf ~ind "modelbuild" "--> invert_right: %t@."
        format_state ;
      let mu = invert_right_ ~lforms ~state ?lact f in
      dprintf ~ind "modelbuild" "<-- invert_right: @[%a@]@." format_meval mu ;
      mu
    end

  and invert_right_ ~lforms ~state ?(lact=[]) f =
    match f.Form.form with
    | Atom (NEG, l, [])
    | Shift {form = Atom (POS, l, []) ; _} ->
        let state = {state with right = Some l} in
        invert_left ~lforms ~state lact
    | And (NEG, f1, f2) -> begin
        match invert_right ~lforms ~state ~lact f1 with
        | Valid ->
            invert_right ~lforms ~state ~lact f2
        | Counter _ as mu -> mu
      end
    | True NEG ->
        Valid
    | Implies (f1, f2) ->
        invert_right ~lforms ~state ~lact:(f1 :: lact) f2
    | Atom (POS, _, _) | And (POS, _, _) | True POS | Or _ | False ->
        bugf "invert_right: positive formula %a" format_form f
    | Shift _ ->
        bugf "invert_right: invalid shift: %a" format_form f
    | Atom _ | Forall _ | Exists _ -> first_order f

  type side = L | R
  let other = function L -> R | R -> L

  let add_left_atoms lforms =
    let known = IdtMap.fold begin fun l lf known ->
        match lf.place, lf.Form.skel with
        | Left _, {form = Atom (_, a, []) ; _} when not (IdtMap.mem a lforms) ->
            IdtSet.add a known
        | _ ->
            known
      end lforms IdtSet.empty in
    (* dprintf "modelbuild" "Known atoms: %a@." IdtSet.pp known ; *)
    let rec walk lforms side f =
      (* dprintf "modelbuild" "%s-walking: %a@." (match side with L -> "left" | _ -> "right") format_form f ; *)
      match f.form with
      | Atom (pol, l, []) ->
          if side = R || pol = NEG || IdtSet.mem l known || IdtMap.mem l lforms then lforms else begin
            (* dprintf "modelbuild" "Adding latom %s@." l.rep ; *)
            IdtMap.add l {
              place = Left Local ;
              label = l ;
              args = [] ;
              skel = f
            } lforms
          end
      | And (_, f1, f2)
      | Or (f1, f2) ->
          let lforms = walk lforms side f1 in
          walk lforms side f2
      | Implies (f1, f2) ->
          let lforms = walk lforms (other side) f1 in
          walk lforms side f2
      | True _ | False ->
          lforms
      | Shift f ->
          walk lforms side f
      | Atom _ | Exists _ | Forall _ -> first_order f
    in
    IdtMap.fold begin fun _ lf lforms ->
      let side = match lf.place with Left _ -> L | _ -> R in
      walk lforms side lf.Form.skel
    end lforms lforms

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

  let build res =
    let lforms = add_left_atoms res.lforms in
    dprintf "modelbuild"
      "@[<v0>Full labeled set:@,  %t@]@."
      (fun ff ->
         let (_, first), rest = IdtMap.pop lforms in
         format_lform ff first ;
         IdtMap.iter (fun _ f -> Format.fprintf ff "@,  @[%a@]" format_lform f) rest) ;
    let right = Some res.goal.Form.label in
    let left = IdtMap.fold begin fun l lf live ->
        match lf.place with
        | Left (Global | Pseudo) -> IdtSet.add lf.Form.label live
        | _ -> live
      end res.lforms IdtSet.empty in
    let left =
      match maximally_extend ~lforms ~left:IdtSet.empty ~right left with
      | Seen -> left
      | New left -> left
      | Subsumed -> bugf "Goal is actually subsumed!"
    in
    let state = {left ; right ; old_rights = IdtSet.empty} in
    let mu = decision ~lforms ~state in
    if compress_model then compress_meval mu else mu

end
