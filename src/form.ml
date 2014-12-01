(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014  INRIA (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Idt
open Term

type neg = NEG
type pos = POS

type _ form =
  | Down    : neg form            -> pos form
  | Patm    : idt * term list     -> pos form
  | Pand    : pos form * pos form -> pos form
  | Ptrue   :                        pos form
  | Or      : pos form * pos form -> pos form
  | False   :                        pos form
  | Exists  : idt * pos form      -> pos form

  | Up      : pos form            -> neg form
  | Natm    : idt * term list     -> neg form
  | Nand    : neg form * neg form -> neg form
  | Ntrue   :                        neg form
  | Implies : pos form * neg form -> neg form
  | Forall  : idt * neg form      -> neg form

let rec app_form : type t. sub -> t form -> t form =
  fun ss f0 -> match f0 with
    | Down nf          -> Down (app_form ss nf)
    | Patm (p, ts)     -> Patm (p, List.map (app_term ss) ts)
    | Pand (pf1, pf2)  -> Pand (app_form ss pf1, app_form ss pf2)
    | Ptrue            -> Ptrue
    | Or (pf1, pf2)    -> Or (app_form ss pf1, app_form ss pf2)
    | False            -> False
    | Exists (x, pf)   -> Exists (x, app_form (bump ss 1) pf)

    | Up pf            -> Up (app_form ss pf)
    | Natm (p, ts)     -> Natm (p, List.map (app_term ss) ts)
    | Nand (nf1, nf2)  -> Nand (app_form ss nf1, app_form ss nf2)
    | Ntrue            -> Ntrue
    | Implies (pf, nf) -> Implies (app_form ss pf, app_form ss nf)
    | Forall (x, nf)   -> Forall (x, app_form (bump ss 1) nf)

let rec replace : type t. ?depth:int -> repl:term IdtMap.t -> t form -> t form =
  fun ?(depth=0) ~repl f0 -> match f0 with
    | Down nf          -> Down (replace ~depth ~repl nf)
    | Patm (p, ts)     -> Patm (p, List.map (Term.replace ~depth ~repl) ts)
    | Pand (pf1, pf2)  -> Pand (replace ~depth ~repl pf1, replace ~depth ~repl pf2)
    | Ptrue            -> Ptrue
    | Or (pf1, pf2)    -> Or (replace ~depth ~repl pf1, replace ~depth ~repl pf2)
    | False            -> False
    | Exists (x, pf)   -> Exists (x, replace ~depth:(depth + 1) ~repl pf)

    | Up pf            -> Up (replace ~depth ~repl pf)
    | Natm (p, ts)     -> Natm (p, List.map (Term.replace ~depth ~repl) ts)
    | Nand (nf1, nf2)  -> Nand (replace ~depth ~repl nf1, replace ~depth ~repl nf2)
    | Ntrue            -> Ntrue
    | Implies (pf, nf) -> Implies (replace ~depth ~repl pf, replace ~depth ~repl nf)
    | Forall (x, nf)   -> Forall (x, replace ~depth:(depth + 1) ~repl nf)

let is_pos : type s. s form -> bool =
  function
    | Down _   -> true
    | Patm _   -> true
    | Pand _   -> true
    | Ptrue    -> true
    | Or _     -> true
    | False    -> true
    | Exists _ -> true
    | _        -> false
let is_neg f = not @@ is_pos f

let mk_pos : type t. t form -> pos form =
  fun f0 -> match f0 with
    | Down nf   -> f0
    | Patm _    -> f0
    | Pand _    -> f0
    | Ptrue     -> f0
    | Or _      -> f0
    | False     -> f0
    | Exists _  -> f0
    | Up pf     -> pf
    | Natm _    -> Down f0
    | Nand _    -> Down f0
    | Ntrue     -> Down f0
    | Implies _ -> Down f0
    | Forall _  -> Down f0

let mk_neg : type t. t form -> neg form =
  fun f0 -> match f0 with
    | Down nf   -> nf
    | Patm _    -> Up f0
    | Pand _    -> Up f0
    | Ptrue     -> Up f0
    | Or _      -> Up f0
    | False     -> Up f0
    | Exists _  -> Up f0
    | Up _      -> f0
    | Natm _    -> f0
    | Nand _    -> f0
    | Ntrue     -> f0
    | Implies _ -> f0
    | Forall _  -> f0

let _Patm p ts = Patm (p, ts)
let _Natm n ts = Natm (n, ts)
let _Pand f1 f2 = Pand (mk_pos f1, mk_pos f2)
let _Or f1 f2 = Or (mk_pos f1, mk_pos f2)
let _Exists x f = Exists (x, mk_pos f)
let _Nand f1 f2 = Nand (mk_neg f1, mk_neg f2)
let _Implies f1 f2 = Implies (mk_pos f1, mk_neg f2)
let _Forall x f = Forall (x, mk_neg f)

type place = Left | Right
let change = function Left -> Right | Right -> Left

type label = idt option ref

let fresh_label =
  let last = ref 0 in
  fun () ->
    incr last ;
    intern @@ "%" ^ string_of_int !last

type lform =
  | L : place * idt * term list * 'a form -> lform

let unvar t = match t.term with
  | Var v -> v
  | _ -> assert false

let relabel ?(place=Right) f =
  let lforms : lform list ref = ref [] in
  let emit lf = lforms := lf :: !lforms in
  let rec spin : type t. place -> term list -> t form -> t form =
    fun place args f0 -> match f0 with
      | Down nf ->
          let lab = fresh_label () in
          let nf = spin place args nf in
          emit (L (place, lab, args, nf)) ;
          Down (Natm (lab, args))
      | Patm (p, ts) ->
          emit (L (place, p, ts, f0)) ; f0
      | Pand (pf1, pf2)  ->
          Pand (spin place args pf1, spin place args pf2)
      | Or (pf1, pf2)    ->
          Or (spin place args pf1, spin place args pf2)
      | Ptrue -> f0
      | False -> f0
      | Exists (x, pf) -> begin
          let v = fresh_var (match place with Right -> `evar | Left -> `param) in
          let pf = app_form (Cons (Shift 0, v)) pf in
          let pf = spin place (v :: args) pf in
          let pf = app_form (Shift 1) pf in
          let pf = replace ~depth:0 ~repl:(IdtMap.digest [unvar v, idx 0]) pf in
          Exists (x, pf)
        end

      | Up pf ->
          let lab = fresh_label () in
          let pf = spin place args pf in
          emit (L (place, lab, args, pf)) ;
          Up (Patm (lab, args))
      | Natm (n, ts) ->
          emit (L (place, n, ts, f0)) ; f0
      | Nand (nf1, nf2) ->
          Nand (spin place args nf1, spin place args nf2)
      | Ntrue -> f0
      | Implies (pf, nf) ->
          Implies (spin (change place) args pf, spin place args nf)
      | Forall (x, nf) -> begin
          let v = fresh_var (match place with Left -> `evar | Right -> `param) in
          let nf = app_form (Cons (Shift 0, v)) nf in
          let nf = spin place (v :: args) nf in
          let nf = app_form (Shift 1) nf in
          let nf = replace ~depth:0 ~repl:(IdtMap.digest [unvar v, idx 0]) nf in
          Forall (x, nf)
        end
  in
  let l0 = fresh_label () in
  emit (L (place, l0, [], spin place [] f)) ;
  !lforms

(*
module Test = struct
  let (x, y, z) = (intern "x", intern "y", intern "z")
  let a = _Forall x @@ _Patm (intern "a") [idx 0]
  let b = _Exists x @@ _Forall y @@ _Forall z @@ _Patm (intern "b") [idx 2 ; idx 1 ; idx 0]
  let c = _Patm (intern "c") []

  let f0 = _Implies b (_Or b c)
end
*)
