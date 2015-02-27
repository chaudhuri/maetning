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

type t = skeleton
and skeleton =
  | Prem

  | InitL
  | InitR

  | TensL  of t
  | TensR  of t * t

  | OneR
  | OneL   of t

  | PlusL  of t * t
  | PlusR1 of t
  | PlusR2 of t

  | ZeroL

  | WithR  of t * t
  | WithL1 of t
  | WithL2 of t

  | TopR

  | ImpR   of t
  | ImpL   of t * t

  | AllR   of t
  | AllL   of t

  | ExR    of t
  | ExL    of t

  | FocR   of t
  | FocL   of idt * t

  | BlurR  of t
  | BlurL  of t

  | Store  of t

let format_skeleton ff sk =
  let open Format in
  let rec spin ff sk =
    match sk with
    | Prem -> fprintf ff "Prem"
    | InitL -> fprintf ff "InitL"
    | InitR -> fprintf ff "InitR"
    | TensL sk -> unary ff "TensL" sk
    | TensR (sk1, sk2) -> binary ff "TensR" sk1 sk2
    | OneR -> fprintf ff "OneR"
    | OneL sk -> unary ff "OneL" sk
    | PlusL (sk1, sk2) -> binary ff "PlusL" sk1 sk2
    | PlusR1 sk -> unary ff "PlusR1" sk
    | PlusR2 sk -> unary ff "PlusR2" sk

    | ZeroL -> fprintf ff "ZeroL"

    | WithR (sk1, sk2) -> binary ff "WithR" sk1 sk2
    | WithL1 sk -> unary ff "WithL1" sk
    | WithL2 sk -> unary ff "WithL2" sk

    | TopR -> fprintf ff "TopR"

    | ImpR sk -> unary ff "ImpR" sk
    | ImpL (sk1, sk2) -> binary ff "ImpL" sk1 sk2

    | AllR sk -> unary ff "ALlR" sk
    | AllL sk -> unary ff "AllL" sk

    | ExR sk -> unary ff "ExR" sk
    | ExL sk -> unary ff "ExL" sk

    | FocR sk -> unary ff "FocR" sk
    | FocL (x, sk) -> fprintf ff "FocL(%s,%a)" x.rep spin sk

    | BlurR sk -> unary ff "BlurR" sk
    | BlurL sk -> unary ff "BlurL" sk

    | Store sk -> unary ff "Store" sk

  and unary ff nm sk =
    fprintf ff "%s(%a)" nm spin sk

  and binary ff nm sk1 sk2 =
    fprintf ff "%s(%a,%a)" nm spin sk1 spin sk2
  in
  spin ff sk

let graft ~premise sk =
  let rec trav sk =
    (* Format.printf "Grafting: %a to %a@." format_skeleton premise format_skeleton sk ; *)
    match sk with
    | InitL | InitR | OneR | ZeroL | TopR -> None

    | Prem             -> Some premise

    | TensL sk         -> unary  ~mk:(fun sk -> TensL sk) sk
    | TensR (sk1, sk2) -> binary ~mk:(fun sk1 sk2 -> TensR (sk1, sk2)) sk1 sk2

    | OneL sk          -> unary  ~mk:(fun sk -> OneL sk) sk

    | PlusL (sk1, sk2) -> binary ~mk:(fun sk1 sk2 -> PlusL (sk1, sk2)) sk1 sk2
    | PlusR1 sk        -> unary  ~mk:(fun sk -> PlusR1 sk) sk
    | PlusR2 sk        -> unary  ~mk:(fun sk -> PlusR2 sk) sk

    | WithR (sk1, sk2) -> binary ~mk:(fun sk1 sk2 -> WithR (sk1, sk2)) sk1 sk2
    | WithL1 sk        -> unary  ~mk:(fun sk -> WithL1 sk) sk
    | WithL2 sk        -> unary  ~mk:(fun sk -> WithL2 sk) sk

    | ImpR sk          -> unary  ~mk:(fun sk -> ImpR sk) sk
    | ImpL (sk1, sk2)  -> binary ~mk:(fun sk1 sk2 -> ImpL (sk1, sk2)) sk1 sk2

    | AllR sk          -> unary  ~mk:(fun sk -> AllR sk) sk
    | AllL sk          -> unary  ~mk:(fun sk -> AllL sk) sk

    | ExR sk           -> unary  ~mk:(fun sk -> ExR sk) sk
    | ExL sk           -> unary  ~mk:(fun sk -> ExL sk) sk

    | FocR sk          -> unary  ~mk:(fun sk -> FocR sk) sk
    | FocL (p, sk)     -> unary  ~mk:(fun sk -> FocL (p, sk)) sk

    | BlurR sk         -> unary  ~mk:(fun sk -> BlurR sk) sk
    | BlurL sk         -> unary  ~mk:(fun sk -> BlurL sk) sk

    | Store sk         -> unary  ~mk:(fun sk -> Store sk) sk

  and unary ~mk sk =
    match trav sk with
    | Some sk -> Some (mk sk)
    | None -> None

  and binary ~mk sk1 sk2 =
    match trav sk1 with
    | Some sk1 -> Some (mk sk1 sk2)
    | None -> begin
        match trav sk2 with
        | Some sk2 -> Some (mk sk1 sk2)
        | None -> None
      end
  in
  trav sk


exception Skelstack

let reduce stack =
  let reduce_one g premise =
    match graft ~premise g with
    | None -> raise Skelstack
    | Some g -> g
  in
  (* Format.printf "Before reduce@." ; *)
  let sk =
    match stack with
    | [] -> raise Skelstack
    | g :: prems -> List.fold_left reduce_one g prems
  in
  (* Format.printf "After reduce@." ; *)
  sk
