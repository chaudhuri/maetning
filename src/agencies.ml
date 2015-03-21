(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries

open Term
open Form
open Seqproof

let (fresh_hyp, fresh_const) =
  let last = ref 0 in
  let fresh_hyp () =
    incr last ;
    Idt.intern ("$" ^ string_of_int !last)
  in
  let fresh_const () =
    incr last ;
    Term.app (Idt.intern ("$" ^ string_of_int !last)) []
  in
  (fresh_hyp, fresh_const)

module Trivial (C : sig type cert end)
  : AGENCY with type cert = C.cert =
struct
  type cert = C.cert

  let ex_InitR sq _ =
    Choices (List.init (List.length sq.left_passive) (fun x -> x))

  let ex_InitL sq _ =
    Choices []

  let cl_TensL sq c =
    match sq.left_active with
    | (x, {form = And (POS, _, _) ; _}) :: _ ->
        let xl = fresh_hyp () in
        let xr = fresh_hyp () in
        Choices [(xl, xr, c)]
    | _ -> Invalid "TensL"

  let ex_TensR sq c =
    match sq.right.form with
    | And (POS, _, _) ->
        Choices [(c, c)]
    | _ -> Invalid "TensR"

  let cl_OneL sq c =
    match sq.left_active with
    | (x, {form = True POS ; _}) :: _ ->
        Choices [c]
    | _ -> Invalid "OneL"

  let ex_OneR sq c =
    match sq.right.form with
    | True POS ->
        Choices []
    | _ -> Invalid "OneR"

  let cl_PlusL sq c =
    match sq.left_active with
    | (x, {form = Or _ ; _}) :: _ ->
        let xx = fresh_hyp () in
        Choices [((xx, c), (xx, c))]
    | _ -> Invalid "PlusL"

  let ex_PlusR sq c =
    match sq.right.form with
    | Or _ ->
        Choices [(`left, c) ; (`right, c)]
    | _ -> Invalid "PlusR"

  let cl_ZeroL sq c =
    match sq.left_active with
    | (x, {form = False ; _}) :: _ ->
        Choices []
    | _ -> Invalid "ZeroL"

  let ex_WithL sq c =
    match sq.left_active with
    | (x, {form = And (NEG, _, _) ; _}) :: _ ->
        let xx = fresh_hyp () in
        Choices [(`left, (xx, c)) ; (`right, (xx, c))]
    | _ -> Invalid "WithL"

  let cl_WithR sq c =
    match sq.right.form with
    | And (NEG, _, _) ->
        Choices [(c, c)]
    | _ -> Invalid "WithR"

  let cl_TopR sq c =
    match sq.right.form with
    | True NEG ->
        Choices []
    | _ -> Invalid "TopR"

  let ex_ImpL sq c =
    match sq.left_active with
    | (x, {form = Implies _ ; _}) :: _ ->
        let xx = fresh_hyp () in
        Choices [(c, (xx, c))]
    | _ -> Invalid "ImpL"

  let cl_ImpR sq c =
    match sq.right.form with
    | Implies _ ->
        let xx = fresh_hyp () in
        Choices [(xx, c)]
    | _ -> Invalid "ImpR"

  let ex_AllL sq c =
    match sq.left_active with
    | (x, {form = Forall _ ; _}) :: _ ->
        let t = Term.fresh_var `evar in
        let xx = fresh_hyp () in
        Choices [(t, (xx, c))]
    | _ -> Invalid "AllL"

  let cl_AllR sq c =
    match sq.right.form with
    | Forall _ ->
        let xx = fresh_const () in
        Choices [(xx, c)]
    | _ -> Invalid "AllR"

  let cl_ExL sq c =
    match sq.left_active with
    | (x, {form = Exists _ ; _}) :: _ ->
        let u = fresh_const () in
        let xx = fresh_hyp () in
        Choices [(u, (xx, c))]
    | _ -> Invalid "ExL"

  let ex_ExR sq c =
    match sq.right.form with
    | Exists _ ->
        let t = Term.fresh_var `evar in
        Choices [(t, c)]
    | _ -> Invalid "ExR"

  let ex_BlurR sq c =
    match polarity sq.right with
    | NEG ->
        Choices [c]
    | _ -> Invalid "BlurR"

  let ex_BlurL sq c =
    match sq.left_active with
    | [(x, f)] when polarity f = POS ->
        Choices [c]
    | _ -> Invalid "BlurL"

  let cl_Store sq c =
    match sq.left_active with
    | _ :: _ ->
        let xx = fresh_hyp () in
        Choices [(xx, c)]
    | _ -> Invalid "Store"

  let ex_Foc sq c =
    match sq.left_active, polarity sq.right with
    | [], POS ->
        let xx = fresh_hyp () in
        Choices (`right c ::
                 List.map (fun (x, _) -> `left (x, (xx, c))) sq.left_passive)
    | _ -> Invalid "Foc"

end

