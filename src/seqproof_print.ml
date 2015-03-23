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

let pprintf = Config.pprintf

let print ~lforms ~goal proof =
  let lf_dict = List.fold_left begin
      fun dict lf ->
        IdtMap.add lf.label lf dict
    end IdtMap.empty lforms in

  let expand_lf f = match f.form with
    | Atom (pol, p, ts) -> begin
        match IdtMap.find p lf_dict with
        | lf ->
            let repl = List.fold_left2 begin
                fun repl lfarg arg ->
                  IdtMap.add (unvar lfarg) arg repl
              end IdtMap.empty lf.args ts
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
            pprintf "<ul><li><code>%a</code> [right-init on <code>%s</code>]</li></ul>@."
              format_sequent sq h.rep
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
                pprintf "<ul><li><code>%a</code> [left-init]</li></ul>@."
                  format_sequent sq
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
    pprintf "<ul><li><code>%a</code><br>@." format_sequent sq ; begin
      match pf with
      | FocR pf ->
          pprintf "right-focus@." ;
          right_focus0 sq pf
      | FocL (h, (x, pf)) -> begin
          match snd @@ List.assoc h sq.left_passive with
          | a ->
              let sq = {sq with left_active = [(x, a)]} in
              pprintf "left-focus on <code>%s</code>,@." h.rep ;
              left_focus0 sq pf
          | exception Not_found -> failwith "FocL/badindex"
        end
      | _ -> failwith "Invalid: frontier"
    end ; pprintf "</li>@.</ul>@."

  and right_focus0 sq pf =
    (* pprintf "<ul><li><code>%a</code> [right-focus]@." format_sequent sq ; *)
    right_focus sq pf ;
    (* pprintf "</li>@.</ul>@." *)

  and left_focus0 sq pf =
    (* pprintf "<ul><li><code>%a</code> [left-focus]@." format_sequent sq ; *)
    (* pprintf "<ul><li><code>%a</code>@." format_sequent sq ; *)
    pprintf "<em>i.e.</em>, <code>%a</code>@." format_sequent sq ;
    left_focus sq pf ;
    (* pprintf "</li>@.</ul>@." *)

  in

  let _goal = {goal with left_passive = List.map expand_lf2 goal.left_passive ;
                        right = expand_lf goal.right}
  in

  frontier goal proof ;
