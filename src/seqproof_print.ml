(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries

open Idt
open Term
open Form
open Seqproof

module M = Idt.IdtMap

let pprintf = Config.pprintf

let expand_fully ~dict f0 =
  let rec spin f =
    match f.form with
    | Atom (pol, p, ts) -> begin
        match M.find p dict with
        | lf ->
            let repl = List.fold_left2 begin
                fun repl lfarg arg ->
                  M.add (unvar lfarg) arg repl
              end M.empty lf.args ts
            in
            Form.replace ~repl lf.skel |> spin
        | exception Not_found -> f
      end
    | And (pol, f1, f2) -> conj ~pol [spin f1 ; spin f2]
    | Or (f1, f2) -> disj [spin f1 ; spin f2]
    | True _ | False -> f
    | Implies (f1, f2) -> implies [spin f1] (spin f2)
    | Exists (x, f) -> exists x (spin f)
    | Forall (x, f) -> forall x (spin f)
    | Shift f -> shift (spin f)
  in
  spin f0

let maybe_unshift f =
  match f.form with
  | Shift f -> f
  | _ -> f

let format_form_shift1 pol_test ff f =
  let f = maybe_unshift f in
  let pol = polarity f in
  if pol_test pol f then format_form () ff f else
  let op = match pol with
    | NEG -> Pretty.STR "↓"
    | POS -> Pretty.STR "↑"
  in
  Pretty.(Opapp (__shift_prec, Prefix (op, pretty_form f))
          |> print ff)

let neg_or_atom pol f =
  match pol, f.form with
  | NEG, _
  | _, Atom _ -> true
  | _ -> false

let pos_or_atom pol f =
  match pol, f.form with
  | POS, _
  | _, Atom _ -> true
  | _ -> false

let format_neutral ~dict ff sq =
  let open Format in
  pp_open_vbox ff 0 ; begin
    pp_print_as ff 0 "<pre>" ;
    List.iter begin fun (h, (_, f)) ->
      fprintf ff "%s : @[%a@]@,"
        h.rep (format_form_shift1 neg_or_atom) (expand_fully ~dict f) ;
    end (List.rev sq.left_passive) ;
    List.iter begin fun (_, f) ->
      fprintf ff "[@[%a@]]@,"
        (format_form_shift1 neg_or_atom) (expand_fully ~dict f) ;
    end (List.rev sq.left_active) ;
    fprintf ff "------------------------------@, @[%a@]"
      (format_form_shift1 pos_or_atom) (expand_fully ~dict sq.right) ;
    pp_print_as ff 0 "</pre>" ;
  end ; pp_close_box ff ()

let renumber pf0 =
  let next hmap h =
    let hr = intern ("u" ^ string_of_int (M.cardinal hmap + 1)) in
    let hmap = M.add h hr hmap in
    (hr, hmap)
  in
  let find_default h hmap =
    match M.find h hmap with
    | hr -> hr
    | exception Not_found -> h
  in
  let rec spin hmap pf =
    match pf with
    | InitL | OneR | ZeroL | TopR -> pf
    | InitR h -> InitR (find_default h hmap)
    | TensL (h1, h2, pf) -> TensL (h1, h2, spin hmap pf)
    | TensR (pf1, pf2) -> TensR (spin hmap pf1, spin hmap pf2)
    | OneL pf -> OneL (spin hmap pf)
    | PlusL ((h1, pf1), (h2, pf2)) -> PlusL ((h1, spin hmap pf1), (h2, spin hmap pf2))
    | PlusR1 pf -> PlusR1 (spin hmap pf)
    | PlusR2 pf -> PlusR2 (spin hmap pf)
    | WithL1 (h, pf) -> WithL1 (h, spin hmap pf)
    | WithL2 (h, pf) -> WithL2 (h, spin hmap pf)
    | WithR (pf1, pf2) -> WithR (spin hmap pf1, spin hmap pf2)
    | ImpL (pf1, (h, pf2)) -> ImpL (spin hmap pf1, (h, spin hmap pf2))
    | ImpR (h, pf) -> ImpR (h, spin hmap pf)
    | AllL (t, (h, pf)) -> AllL (t, (h, spin hmap pf))
    | AllR (x, pf) -> AllR (x, spin hmap pf)
    | ExL (x, (h, pf)) -> ExL (x, (h, spin hmap pf))
    | ExR (t, pf) -> ExR (t, spin hmap pf)
    | FocR pf -> FocR (spin hmap pf)
    | FocL (h, (h1, pf)) -> FocL (find_default h hmap, (h1, spin hmap pf))
    | BlurR pf -> BlurR (spin hmap pf)
    | BlurL pf -> BlurL (spin hmap pf)
    | Store (h, pf) ->
        let (hr, hmap) = next hmap h in
        Store (hr, spin hmap pf)
  in
  spin M.empty pf0

let print ~lforms ~goal proof =
  let dict = List.fold_left begin
      fun dict lf ->
        M.add lf.label lf dict
    end M.empty lforms in

  let expand_lf f = match f.form with
    | Atom (pol, p, ts) -> begin
        match M.find p dict with
        | lf ->
            let repl = List.fold_left2 begin
                fun repl lfarg arg ->
                  M.add (unvar lfarg) arg repl
              end M.empty lf.args ts
            in
            Form.replace ~repl lf.skel
        | exception Not_found -> f
      end
    | _ -> f
  in
  let expand_lf2 (x, (l, f)) = (x, (l, expand_lf f)) in

  let rec right_focus sq pf =
    match sq.right.form, pf with
    | Atom (POS, p, pts), InitR h -> begin
        match (snd @@ List.assoc h sq.left_passive).form with
        | Atom (POS, q, qts) when p == q && pts = qts ->
            pprintf "<ul><li>@.%a [right-init with <code>%s</code>]</li></ul>@."
              (format_neutral ~dict) sq h.rep
        | _ -> failwith "InitR/match"
        | exception Not_found -> failwith "InitR/badindex"
      end
    | And (POS, a, b), TensR (pfa, pfb) ->
        right_focus {sq with right = a} pfa ;
        right_focus {sq with right = b} pfb
    | True POS, OneR ->
        ()
    | Or (a, b), PlusR1 pfa ->
        right_focus {sq with right = a} pfa
    | Or (a, b), PlusR2 pfb ->
        right_focus {sq with right = b} pfb
    | False, _ ->
        failwith "FalseR"
    | Exists (x, a), ExR (t, pfa) ->
        let a = app_form (Cons (Shift 0, t)) a in
        right_focus {sq with right = a} pfa
    | Shift a, BlurR pf ->
        let sq = {sq with right = a} in
        right_active sq pf
    | _ -> failwith "Invalid: right focus"

  and left_focus sq pf =
    match sq.left_active with
    | [(x0, f)] -> begin
        match f.form, pf with
        | Atom (NEG, p, pts), InitL -> begin
            match sq.right.form with
            | Atom (NEG, q, qts) when p == q && pts = qts ->
                pprintf "<ul><li>@.%a [left-init]</li></ul>@."
                  (format_neutral ~dict) sq
            | _ -> failwith "InitL/match"
          end
        | And (NEG, a, b), WithL1 (x, pf) ->
            let sq = {sq with left_active = [(x, a)]} in
            left_focus sq pf
        | And (NEG, a, b), WithL2 (x, pf) ->
            let sq = {sq with left_active = [(x, b)]} in
            left_focus sq pf
        | True NEG, _ ->
            failwith "TopL"
        | Implies (a, b), ImpL (pfa, (x, pfb)) ->
            let sqa = {sq with left_active = [] ; right = a} in
            right_focus sqa pfa ;
            let sqb = {sq with left_active = [(x, b)]} in
            left_focus sqb pfb
        | Forall (_, a), AllL (t, (x, pf)) ->
            let a = app_form (Cons (Shift 0, t)) a in
            let sq = {sq with left_active = [(x, a)]} in
            left_focus sq pf
        | Shift a, BlurL pf ->
            let sq = {sq with left_active = [(x0, a)]} in
            left_active sq pf
        | _ -> failwith "Invalid: left focus"
      end
    | _ -> failwith "Invalid: too many left foci"

  and right_active sq pf =
    match sq.right.form, pf with
    | Atom (NEG, _, _), _ ->
        let sq = {sq with right = expand_lf sq.right} in
        left_active sq pf
    | Shift a, _ ->
        let sq = {sq with right = expand_lf a} in
        left_active sq pf
    | And (NEG, a, b), WithR (pfa, pfb) ->
        right_active {sq with right = a} pfa ;
        right_active {sq with right = b} pfb
    | True NEG, TopR ->
        ()
    | Implies (a, b), ImpR (x, pf) ->
        let sq = {sq with left_active = (x, a) :: sq.left_active ;
                          right = b} in
        right_active sq pf
    | Forall (x, a), AllR (u, pf) ->
        let a = app_form (Cons (Shift 0, Term.app u [])) a in
        let sq = {sq with right = a} in
        right_active sq pf
    | _ -> failwith "Invalid: right active"

  and left_active sq pf =
    match sq.left_active with
    | [] -> frontier sq pf
    | (_, f0) :: rest -> begin
        match f0.form, pf with
        | Atom (POS, p, _), Store (x, pf) ->
            let sq = {sq with left_active = rest ;
                              left_passive = (x, (p, expand_lf f0))
                                             :: sq.left_passive} in
            left_active sq pf
        | Shift ({form = Atom (NEG, lab, _) ; _} as a), Store (x, pf) ->
            let a = expand_lf a in
            let sq = {sq with left_active = rest ;
                              left_passive = (x, (lab, a))
                                             :: sq.left_passive} in
            left_active sq pf
        | And (POS, a, b), TensL (x, y, pf) ->
            let sq = {sq with left_active = (x, a) :: (y, b) :: rest} in
            left_active sq pf
        | True POS, OneL pf ->
            let sq = {sq with left_active = rest} in
            left_active sq pf
        | Or (a, b), PlusL ((x, pfa), (y, pfb)) ->
            let sqa = {sq with left_active = (x, a) :: rest} in
            left_active sqa pfa ;
            let sqb = {sq with left_active = (y, b) :: rest} in
            left_active sqb pfb
        | False, ZeroL ->
            ()
        | Exists (_, a), ExL (u, (x, pf)) ->
            let a = app_form (Cons (Shift 0, Term.app u [])) a in
            let sq = {sq with left_active = (x, a) :: rest} in
            left_active sq pf
        | _ -> failwith "Invalid: left active"
      end

  and frontier sq pf =
    pprintf "<ul><li>@.%a@." (format_neutral ~dict) sq ; begin
      match pf with
      | FocR pf ->
          pprintf "right-focus@." ;
          right_focus0 sq pf
      | FocL (h, (x, pf)) -> begin
          match snd @@ List.assoc h sq.left_passive with
          | a ->
              let sq = {sq with left_active = [(x, a)]} in
              pprintf "left-focus on <code>%s</code>@." h.rep ;
              left_focus0 sq pf
          | exception Not_found -> failwith "FocL/badindex"
        end
      | _ -> failwith "Invalid: frontier"
    end ; pprintf "</li>@.</ul>@."

  and right_focus0 sq pf =
    (* pprintf "<ul><li>@.%a [right-focus]@." format_neutral sq ; *)
    right_focus sq pf ;
    (* pprintf "</li>@.</ul>@." *)

  and left_focus0 sq pf =
    (* pprintf "<ul><li><code>%a</code> [left-focus]@." format_neutral sq ; *)
    (* pprintf "<ul><li><code>%a</code>@." format_neutral sq ; *)
    (* pprintf "<em>i.e.</em>, <code>%a</code>@." format_neutral sq ; *)
    left_focus sq pf ;
    (* pprintf "</li>@.</ul>@." *)

  in

  let _goal = {goal with left_passive = List.map expand_lf2 goal.left_passive ;
                        right = expand_lf goal.right}
  in

  frontier goal (renumber proof)
