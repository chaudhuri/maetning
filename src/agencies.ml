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

module Trivial (C : sig type cert val format_cert : Format.formatter -> cert -> unit end)
  : AGENCY with type cert = C.cert =
struct
  include C

  let ex_InitR sq _ =
    Choices (List.map fst sq.left_passive)

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
    match sq.right.form with
    | Shift _ -> Choices [c]
    | _ -> Invalid "BlurR"

  let ex_BlurL sq c =
    match sq.left_active with
    | [(x, {form = Shift _ ; _})] ->
        Choices [c]
    | _ -> Invalid "BlurL"

  let cl_Store sq c =
    match sq.left_active with
    | _ :: _ ->
        let xx = fresh_hyp () in
        Choices [(xx, c)]
    | _ -> Invalid "Store"

  let ex_Foc sq c =
    match sq.left_active, polarity sq.right, sq.right.form with
    | [], POS, _
    | [], _, Atom (NEG, _, _) ->
        let xx = fresh_hyp () in
        Choices (`right c ::
                 List.map (fun (x, _) -> `left (x, (xx, c))) sq.left_passive)
    | _ -> Invalid "Foc"

end

module Rebuild : AGENCY with type cert = Skeleton.t = struct

  open Skeleton

  type cert = Skeleton.t

  let format_cert = Skeleton.format_skeleton

  let ex_InitR sq cc =
    match sq.right.form, cc with
    | Atom (POS, p, _), InitR -> begin
        let suitable (x, (_, f)) =
          match f.form with
          | Atom (POS, q, _) when p == q -> Some x
          | _ -> None
        in
        match List.filter_map suitable sq.left_passive with
        | [] -> Invalid "InitR: no choices"
        | cs -> Choices cs
      end
    | _ -> Invalid "InitR"

  let ex_InitL sq cc =
    match sq.left_active, cc with
    | [_, {form = Atom (NEG, p, _) ; _}], InitL -> Choices []
    | _ -> Invalid "InitL"

  let cl_TensL sq cc =
    match sq.left_active, cc with
    | ((_, {form = And (POS, _, _) ; _}) :: _), TensL cc ->
        let xl = fresh_hyp () in
        let xr = fresh_hyp () in
        Choices [(xl, xr, cc)]
    | _ -> Invalid "TensL"

  let ex_TensR sq cc =
    match sq.right.form, cc with
    | And (POS, _, _), TensR (ccl, ccr) ->
        Choices [(ccl, ccr)]
    | _ -> Invalid "TensR"

  let cl_OneL sq cc =
    match sq.left_active, cc with
    | ((x, {form = True POS ; _}) :: _), OneL cc ->
        Choices [cc]
    | _ -> Invalid "OneL"

  let ex_OneR sq cc =
    match sq.right.form, cc with
    | True POS, OneR ->
        Choices []
    | _ -> Invalid "OneR"

  let cl_PlusL sq cc =
    match sq.left_active, cc with
    | ((x, {form = Or _ ; _}) :: _), PlusL (ccl, ccr) ->
        let xx = fresh_hyp () in
        Choices [((xx, ccl), (xx, ccr))]
    | _ -> Invalid "PlusL"

  let ex_PlusR sq cc =
    match sq.right.form, cc with
    | Or _, PlusR1 cc -> Choices [(`left, cc)]
    | Or _, PlusR2 cc -> Choices [(`right, cc)]
    | _ -> Invalid "PlusR"

  let cl_ZeroL sq cc =
    match sq.left_active, cc with
    | ((x, {form = False ; _}) :: _), ZeroL ->
        Choices []
    | _ -> Invalid "ZeroL"

  let ex_WithL sq cc =
    match sq.left_active with
    | (x, {form = And (NEG, _, _) ; _}) :: _ -> begin
        let xx = fresh_hyp () in
        match cc with
        | WithL1 cc -> Choices [(`left, (xx, cc))]
        | WithL2 cc -> Choices [(`right, (xx, cc))]
        | _ -> Invalid "WithL"
      end
    | _ -> Invalid "WithL"

  let cl_WithR sq cc =
    match sq.right.form, cc with
    | And (NEG, _, _), WithR (ccl, ccr) ->
        Choices [(ccl, ccr)]
    | _ -> Invalid "WithR"

  let cl_TopR sq cc =
    match sq.right.form, cc with
    | True NEG, TopR ->
        Choices []
    | _ -> Invalid "TopR"

  let ex_ImpL sq cc =
    match sq.left_active, cc with
    | ((x, {form = Implies _ ; _}) :: _), ImpL (cca, ccb) ->
        let xx = fresh_hyp () in
        Choices [(cca, (xx, ccb))]
    | _ -> Invalid "ImpL"

  let cl_ImpR sq cc =
    match sq.right.form, cc with
    | Implies _, ImpR cc ->
        let xx = fresh_hyp () in
        Choices [(xx, cc)]
    | _ -> Invalid "ImpR"

  let ex_AllL sq cc =
    match sq.left_active, cc with
    | ((x, {form = Forall _ ; _}) :: _), AllL cc ->
        let t = Term.fresh_var `evar in
        let xx = fresh_hyp () in
        Choices [(t, (xx, cc))]
    | _ -> Invalid "AllL"

  let cl_AllR sq cc =
    match sq.right.form, cc with
    | Forall _, AllR cc ->
        let xx = fresh_const () in
        Choices [(xx, cc)]
    | _ -> Invalid "AllR"

  let cl_ExL sq cc =
    match sq.left_active, cc with
    | ((x, {form = Exists _ ; _}) :: _), ExL cc ->
        let u = fresh_const () in
        let xx = fresh_hyp () in
        Choices [(u, (xx, cc))]
    | _ -> Invalid "ExL"

  let ex_ExR sq cc =
    match sq.right.form, cc with
    | Exists _, ExR cc ->
        let t = Term.fresh_var `evar in
        Choices [(t, cc)]
    | _ -> Invalid "ExR"

  let ex_BlurR sq cc =
    match sq.right.form, cc with
    | Shift _, BlurR cc ->
        Choices [cc]
    | _ -> Invalid "BlurR"

  let ex_BlurL sq cc =
    match sq.left_active, cc with
    | ([(x, {form = Shift _ ; _})], BlurL cc) ->
        Choices [cc]
    | _ -> Invalid "BlurL"

  let cl_Store sq cc =
    match sq.left_active, cc with
    | (_ :: _), Store cc ->
        let xx = fresh_hyp () in
        Choices [(xx, cc)]
    | _ -> Invalid "Store"

  let ex_Foc sq cc =
    match sq.left_active, polarity sq.right, sq.right.form with
    | [], POS, _
    | [], _, Atom (NEG, _, _) -> begin
        match cc with
        | FocL (p, cc) ->
            let xx = fresh_hyp () in
            let choices = List.filter_map begin
                fun (x, (l, _)) ->
                  if l == p then
                    Some (`left (x, (xx, cc)))
                  else None
              end sq.left_passive in
            Choices choices
        | FocR cc ->
            Choices [`right cc]
        | _ -> Invalid "Foc"
      end
    | _ -> Invalid "Foc"

end
