(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2016  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

let compress_model       = true
let antecedent_first     = true

(* Model reconstruction based on the algorithm described in:

   Taus Brock-Nannestad and Kaustuv Chaudhuri, "Saturation-based
   Countermodel Construction for Propositional Intuitionistic Logic",
   2016.
*)

open Batteries
module Ft = FingerTree

open Idt
open Term
open Form
open Sequent
open Inverse

open Debug

module IMap = Map.Make (Int)
module ISet = Set.Make (Int)

(******************************************************************************)

module Model : sig
  type model = private {
    assn : IdtSet.t ;
    kids : model list ;
    mid  : int ;
  }

  val model : assn:IdtSet.t -> kids:(model list) -> model
end = struct
  type model = {
    assn : IdtSet.t ;
    kids : model list ;
    mid  : int ;
  }

  let rec same_kids ks1 ks2 =
    match ks1, ks2 with
    | [], [] -> true
    | k1 :: ks1, k2 :: ks2 ->
        k1.mid = k2.mid && same_kids ks1 ks2
    | _ -> false

  module ModTab = Weak.Make (
    struct
      type t = model
      let hash m = Hashtbl.hash (m.assn, m.kids)
      let equal m1 m2 =
        IdtSet.equal m1.assn m2.assn &&
        same_kids m1.kids m2.kids
    end)
  let __models = ModTab.create 19

  let midgen = new Namegen.namegen (fun n -> n)

  let model ~assn ~kids =
    let modl = {mid = midgen#next ; assn ; kids} in
    ModTab.merge __models modl
end

include Model

let rec insert_kid ks k =
  match ks with
  | [] -> [k]
  | kk :: ks ->
      if k.mid < kk.mid then
        kk :: insert_kid ks k
      else k :: kk :: ks

let merge_kids ks1 ks2 = List.fold_left insert_kid ks1 ks2

(******************************************************************************)

let empty_model = model ~assn:IdtSet.empty ~kids:[]

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
  let rec spin_lines seen modl =
    if ISet.mem modl.mid seen then seen else
    let seen = ISet.add modl.mid seen in
    let seen = List.fold_left spin_lines seen modl.kids in
    fprintf dotff "w%d [shape=box,fontname=\"monospace\",fontsize=10,label=\"@[%a@]\"];@."
      modl.mid IdtSet.pp modl.assn ;
    List.iter (fun kid -> fprintf dotff "w%d -> w%d;" modl.mid kid.mid) modl.kids ;
    seen in
  ignore (spin_lines ISet.empty modl) ;
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
          let assn = IdtSet.union m1.assn m2.assn in
          let kids = merge_kids m1.kids m2.kids in
          Counter (model ~assn ~kids)
    end

let forward = function
  | Valid -> Valid
  | Counter modl -> Counter (model ~assn:IdtSet.empty ~kids:[modl])

(******************************************************************************)

exception Model

let first_order f =
  Format.eprintf "Cannot construct countermodels for first-order formulas@.%a@." format_form f ;
  raise Model

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

module type CHECK = sig
  val check : 'a result -> model -> bool
end

module BackwardCheck : CHECK = struct
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
    fprintf ff "@[<hv0>w%d |= {%a},@ @[<b1>[%a]@]"
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

  let check res modl =
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


module ForwardCheck : CHECK = struct
  type side = L | R
  let other = function L -> R | R -> L

  let rec classically_true assn future f =
    BitSet.mem future f.formid &&
    match f.form with
    | Atom (_, l, _) ->
        IdtSet.mem l assn
    | And (_, f1, f2) ->
        classically_true assn future f1 &&
        classically_true assn future f2
    | True _ ->
        true
    | Or (f1, f2) ->
        classically_true assn future f1 ||
        classically_true assn future f2
    | False ->
        false
    | Implies (f1, f2) ->
        (not (classically_true assn future f1) || classically_true assn future f2)
    | Shift f ->
        classically_true assn future f
    | Forall _ | Exists _ -> first_order f

  let compute_classical assn future subfmap =
    IMap.fold begin fun n (f, _) valu ->
      if classically_true assn future f then
        BitSet.add n valu
      else valu
    end subfmap (BitSet.create (IMap.cardinal subfmap))

  let rec compute subfmap modl =
    let valu = BitSet.create_full (IMap.cardinal subfmap) in
    let valu = List.fold_left begin fun valu modl ->
        BitSet.inter valu (compute subfmap modl)
      end valu modl.kids in
    compute_classical modl.assn valu subfmap

  let check res modl =
    let ants = IdtMap.fold begin fun l lf ants ->
        match lf.Form.place with
        | Left Global | Left Pseudo ->
            expand_fully ~lforms:res.lforms lf.Form.skel :: ants
        | _ -> ants
      end res.lforms [] in
    let impl = implies ants (expand_fully ~lforms:res.lforms res.goal.Form.skel) in
    let rec walk subfmap side f =
      let subfmap = IMap.add f.formid (f, side) subfmap in
      match f.form with
      | Atom _ | True _ | False -> subfmap
      | And (_, f1, f2) | Or (f1, f2) ->
          walk (walk subfmap side f1) side f2
      | Implies (f1, f2) ->
          walk (walk subfmap (other side) f1) side f2
      | Shift f ->
          walk subfmap side f
      | Exists _ | Forall _ -> first_order f
    in
    let subfmap = walk IMap.empty R impl in
    let trueset = compute subfmap modl in
    BitSet.mem trueset impl.formid
end

(* module Check = BackwardCheck *)
module Check = ForwardCheck

(******************************************************************************)
(* Model building *)

module Build : sig val build : 'a result -> meval end = struct
  let propify l = (l, [])

  type state = {
    left : IdtSet.t ;
    right : Idt.t option ;
    impos : IdtSet.t ;
  }

  type extend_result =
    | Seen
    | Subsumed
    | New of state

  let maximally_extend ~lforms ~state ls =
    let left = IdtSet.union state.left ls in
    let sq0 = mk_sequent ()
        ~left:(IdtSet.elements left |>
               List.map propify |>
               Ft.of_list)
        ?right:(Option.map propify state.right)
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
    let (left, sq) = IdtMap.fold begin fun _ lf (left, sq) ->
        match lf.Form.place with
        | Left _ ->
            maybe_extend lf.Form.label (left, sq)
        | Right -> (left, sq)
      end lforms (left, sq0) in
    (* Format.eprintf "Extended\n  %a\ninto\n  %a@." (format_sequent ()) sq0 (format_sequent ())sq ; *)
    if IdtSet.equal left state.left then Seen else begin
      let impos =
        IdtMap.fold begin fun _ lf impos ->
          match lf.Form.place with
          | Left _ -> impos
          | Right ->
              let sq = override sq ~right:(Some (lf.Form.label, [])) in
              if Inverse.Data.subsumes ~all:true sq
              then impos
              else IdtSet.add lf.Form.label impos
        end lforms IdtSet.empty
      in
      New {state with left ; impos}
    end

  let compute_impos ~lforms ~left =
    let sq0 = mk_sequent ()
        ~left:(IdtSet.elements left |>
               List.map propify |>
               Ft.of_list)
    in
    IdtMap.fold begin fun _ lf impos ->
      match lf.Form.place with
      | Left _ -> impos
      | Right ->
          let new_sq = override sq0 ~right:(Some (lf.Form.label, [])) in
          if Inverse.Data.subsumes ~all:true new_sq
          then impos
          else IdtSet.add lf.Form.label impos
    end lforms IdtSet.empty

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

  let rec decision ~lforms ~state =
    let format_state ff =
      Format.fprintf ff "@[%a@ |- %a \\ %a@]"
        IdtSet.pp state.left
        format_right state.right
        IdtSet.pp state.impos
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
    cross (fun () -> modl) (fun () -> right_only_decision ~lforms ~state)

  and right_only_decision ~lforms ~state =
    let format_state ff =
      Format.fprintf ff "@[%a@ |- %a \\ %a@]"
        IdtSet.pp state.left
        format_right state.right
        IdtSet.pp state.impos
    in
    with_indent begin fun ind ->
      dprintf ~ind "modelbuild" "--> right_only_decision: %t@." format_state ;
      let mu = right_only_decision_ ~lforms ~state in
      dprintf ~ind "modelbuild" "<-- right_only_decision: @[%a@]@." format_meval mu ;
      mu
    end

  and right_only_decision_ ~lforms ~state =
    let modl = Counter empty_model in
    match state.right with
      | None -> modl
      | Some idt -> begin
          match (IdtMap.find idt lforms).Form.skel with
          | f ->
              if polarity f = NEG then modl else
                cross (fun () -> modl) (fun () -> focus_right ~lforms ~state f)
          | exception Not_found -> modl
        end

  and focus_left ~lforms ~state f =
    let format_state ff =
      Format.fprintf ff "@[%a ; [%a]@ |- %a \\ %a@]"
        IdtSet.pp state.left
        format_form f
        format_right state.right
        IdtSet.pp state.impos
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
        let impos = match state.right with
          | Some rl -> IdtSet.add rl state.impos
          | None -> state.impos
        in
        if IdtSet.mem l impos
        then Valid
        else Counter (model ~assn:(IdtSet.singleton l) ~kids:[])
      end
    | Atom (POS, l, []) ->
        Counter (model ~assn:(IdtSet.singleton l) ~kids:[])
    | And (NEG, f1, f2) ->
        cross
          (fun () -> focus_left ~lforms ~state f1)
          (fun () -> focus_left ~lforms ~state f2)
    | True NEG ->
        Counter empty_model
    | Implies (f1, f2) ->
        if antecedent_first then begin
          match focus_right ~lforms ~state f1 with
          | Valid ->
              focus_left ~lforms ~state f2
          | Counter _ as mu -> mu
        end else begin
          match focus_left ~lforms ~state f2 with
          | Valid ->
              focus_right ~lforms ~state f1
          | Counter _ as mu -> mu
        end
    | And (POS, _, _) | True POS | Or _ | False ->
        bugf "focus_left: positive formula %a" format_form f
    | Atom _ | Forall _ | Exists _ -> first_order f

  and focus_right ~lforms ~state f =
    let format_state ff =
      Format.fprintf ff "@[%a@ |- [%a] \\ %a@]"
        IdtSet.pp state.left
        format_form f
        IdtSet.pp state.impos
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
      Format.fprintf ff "@[%a ;@ %a ;@ %a @ |- %a \\ %a@]"
        IdtSet.pp state.left
        IdtSet.pp (Option.default IdtSet.empty store)
        format_forms fs
        format_right state.right
        IdtSet.pp state.impos
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
        match maximally_extend ~lforms ~state store with
        | Seen -> begin
            right_only_decision ~lforms ~state
          end
        | Subsumed ->
            (* dprintf "modelbuild" "maximal_extend: subsumed@." ; *)
            Valid
        | New state ->
            (* dprintf "modelbuild" "maximal_extend: new@." ; *)
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
      Format.fprintf ff "@[%a ;@ %a@ |- %a \\ %a@]"
        IdtSet.pp state.left
        format_forms (Option.default [] lact)
        format_form f
        IdtSet.pp state.impos
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

  let add_atoms lforms =
    let known = IdtMap.fold begin fun l lf known ->
        match lf.Form.skel with
        | {form = Atom (_, a, []) ; _} when not (IdtMap.mem a lforms) ->
            IdtSet.add a known
        | _ -> known
      end lforms IdtSet.empty in
    (* dprintf "modelbuild" "Known atoms: %a@." IdtSet.pp known ; *)
    let rec walk lforms side f =
      (* dprintf "modelbuild" "%s-walking: %a@." (match side with L -> "left" | _ -> "right") format_form f ; *)
      match f.form with
      | Atom (pol, l, []) ->
          if IdtMap.mem l lforms || IdtSet.mem l known then lforms else
          if side = R && pol = POS then lforms else
          if side = L && pol = NEG then lforms else begin
            (* dprintf "modelbuild" "Adding latom %s@." l.rep ; *)
            IdtMap.add l {
              place = (match side with L -> Left Local | R -> Right) ;
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

  let rec future futs modl =
    let futs = ISet.add modl.mid futs in
    List.fold_left strict_future futs modl.kids

  and strict_future futs modl =
    List.fold_left future futs modl.kids

  let rec compress modl =
    let kids = modl.kids |>
               List.map compress |>
               List.sort (fun m1 m2 -> IdtSet.compare m1.assn m2.assn) |>
               List.unique ~eq:eq_models in
    let futures = List.fold_left strict_future ISet.empty kids in
    let kids = List.filter (fun kid -> not (ISet.mem kid.mid futures)) kids in
    match kids with
    | [kid] when IdtSet.equal modl.assn kid.assn -> kid
    | _ -> model ~assn:modl.assn ~kids

  let compress_meval = function
    | Valid -> Valid
    | Counter modl -> Counter (compress modl)

  let build res =
    let lforms = add_atoms res.lforms in
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
    let state = {left ; right ; impos = IdtSet.empty} in
    let state =
      match maximally_extend ~lforms ~state left with
      | Seen -> state
      | New state -> state
      | Subsumed -> bugf "Goal is actually subsumed!"
    in
    let mu = decision ~lforms ~state in
    if compress_model then compress_meval mu else mu

end
