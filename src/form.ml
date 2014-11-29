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
  | Down    : label * neg form    -> pos form
  | Patm    : idt * term list     -> pos form
  | Pand    : pos form * pos form -> pos form
  | Ptrue   :                        pos form
  | Or      : pos form * pos form -> pos form
  | False   :                        pos form
  | Exists  : idt * pos form      -> pos form

  | Up      : label * pos form    -> neg form
  | Natm    : idt * term list     -> neg form
  | Nand    : neg form * neg form -> neg form
  | Ntrue   :                        neg form
  | Implies : pos form * neg form -> neg form
  | Forall  : idt * neg form      -> neg form

and label = idt option ref

type place = Left | Right
let change = function Left -> Right | Right -> Left

let fresh_label =
  let last = ref 0 in
  fun () ->
    incr last ;
    intern @@ "%" ^ string_of_int !last

let rec relabel : type t. t form -> unit =
  fun f0 -> match f0 with
    | Down (lab, nf)   ->
        lab := Some (fresh_label ()) ;
        relabel nf
    | Patm _           -> ()
    | Pand (pf1, pf2)  -> relabel pf1 ; relabel pf2
    | Or  (pf1, pf2)   -> relabel pf1 ; relabel pf2
    | Ptrue            -> ()
    | False            -> ()
    | Exists (_, pf)   -> relabel pf

    | Up (lab, pf)     ->
        lab := Some (fresh_label ()) ;
        relabel pf
    | Natm _           -> ()
    | Nand (nf1, nf2)  -> relabel nf1 ; relabel nf2
    | Ntrue            -> ()
    | Implies (pf, nf) -> relabel pf ; relabel nf
    | Forall (_, nf)   -> relabel nf

let rec app_form : type t. sub -> t form -> t form =
  fun ss f0 -> match f0 with
    | Down (lab, nf)   -> Down (lab, app_form ss nf)
    | Patm (p, ts)     -> Patm (p, List.map (app_term ss) ts)
    | Pand (pf1, pf2)  -> Pand (app_form ss pf1, app_form ss pf2)
    | Ptrue            -> Ptrue
    | Or (pf1, pf2)    -> Or (app_form ss pf1, app_form ss pf2)
    | False            -> False
    | Exists (x, pf)   -> Exists (x, app_form (bump ss 1) pf)

    | Up (lab, pf)     -> Up (lab, app_form ss pf)
    | Natm (p, ts)     -> Natm (p, List.map (app_term ss) ts)
    | Nand (nf1, nf2)  -> Nand (app_form ss nf1, app_form ss nf2)
    | Ntrue            -> Ntrue
    | Implies (pf, nf) -> Implies (app_form ss pf, app_form ss nf)
    | Forall (x, nf)   -> Forall (x, app_form (bump ss 1) nf)

let rec replace : type t. ?depth:int -> repl:term IdtMap.t -> t form -> t form =
  fun ?(depth=0) ~repl f0 -> match f0 with
    | Down (lab, nf)   -> Down (lab, replace ~depth ~repl nf)
    | Patm (p, ts)     -> Patm (p, List.map (Term.replace ~depth ~repl) ts)
    | Pand (pf1, pf2)  -> Pand (replace ~depth ~repl pf1, replace ~depth ~repl pf2)
    | Ptrue            -> Ptrue
    | Or (pf1, pf2)    -> Or (replace ~depth ~repl pf1, replace ~depth ~repl pf2)
    | False            -> False
    | Exists (x, pf)   -> Exists (x, replace ~depth:(depth + 1) ~repl pf)

    | Up (lab, pf)     -> Up (lab, replace ~depth ~repl pf)
    | Natm (p, ts)     -> Natm (p, List.map (Term.replace ~depth ~repl) ts)
    | Nand (nf1, nf2)  -> Nand (replace ~depth ~repl nf1, replace ~depth ~repl nf2)
    | Ntrue            -> Ntrue
    | Implies (pf, nf) -> Implies (replace ~depth ~repl pf, replace ~depth ~repl nf)
    | Forall (x, nf)   -> Forall (x, replace ~depth:(depth + 1) ~repl nf)
