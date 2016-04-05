(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Fully explicit sequent proofs *)

open Batteries

open Idt
open Term
open Form

type hyp = idt                  (* index of a hypothesis *)
type eig = idt                  (* name of an eigen variable *)

type proof =
  | InitL
  | InitR  of hyp

  | TensL  of proof2
  | TensR  of proof * proof

  | OneL   of proof
  | OneR

  | PlusL  of proof1 * proof1
  | PlusR1 of proof
  | PlusR2 of proof

  | ZeroL

  | WithL1 of proof1
  | WithL2 of proof1
  | WithR  of proof * proof

  | TopR

  | ImpL   of proof * proof1
  | ImpR   of hyp * proof

  | AllL   of term * proof1
  | AllR   of eig * proof

  | ExL    of eig * proof1
  | ExR    of term * proof

  | FocR   of proof
  | FocL   of hyp * proof1

  | BlurR  of proof
  | BlurL  of proof

  | Store  of proof1

and proof1 = hyp * proof
and proof2 = hyp * hyp * proof

let rec replace_proof ?(depth=0) ~repl pf0 =
  match pf0 with
  | InitL | InitR _ | OneR | ZeroL | TopR -> pf0
  | TensL (x, y, pf) ->
      TensL (x, y, replace_proof ~depth ~repl pf)
  | TensR (pf1, pf2) ->
      TensR (replace_proof ~depth ~repl pf1,
             replace_proof ~depth ~repl pf2)
  | OneL pf ->
      OneL (replace_proof ~depth ~repl pf)
  | PlusL (pf1, pf2) ->
      PlusL (replace_proof1 ~depth ~repl pf1,
             replace_proof1 ~depth ~repl pf2)
  | PlusR1 pf ->
      PlusR1 (replace_proof ~depth ~repl pf)
  | PlusR2 pf ->
      PlusR2 (replace_proof ~depth ~repl pf)
  | WithL1 pf1 ->
      WithL1 (replace_proof1 ~depth ~repl pf1)
  | WithL2 pf1 ->
      WithL2 (replace_proof1 ~depth ~repl pf1)
  | WithR (pf1, pf2) ->
      WithR (replace_proof ~depth ~repl pf1,
             replace_proof ~depth ~repl pf2)
  | ImpL (pf1, pf2) ->
      ImpL (replace_proof ~depth ~repl pf1,
            replace_proof1 ~depth ~repl pf2)
  | ImpR (x, pf) ->
      ImpR (x, replace_proof ~depth ~repl pf)
  | AllL (t, pf) ->
      AllL (Term.replace ~depth ~repl t,
            replace_proof1 ~depth ~repl pf)
  | AllR (x, pf) ->
      AllR (x, replace_proof ~depth:(depth + 1) ~repl pf)
  | ExL (u, pf) ->
      ExL (u, replace_proof1 ~depth:(depth + 1) ~repl pf)
  | ExR (t, pf) ->
      ExR (Term.replace ~depth ~repl t,
           replace_proof ~depth ~repl pf)
  | FocR pf ->
      FocR (replace_proof ~depth ~repl pf)
  | FocL (x, pf) ->
      FocL (x, replace_proof1 ~depth ~repl pf)
  | BlurR pf ->
      BlurR (replace_proof ~depth ~repl pf)
  | BlurL pf ->
      BlurL (replace_proof ~depth ~repl pf)
  | Store pf ->
      Store (replace_proof1 ~depth ~repl pf)

and replace_proof1 ~depth ~repl (x, pf) =
  (x, replace_proof ~depth ~repl pf)

(******************************************************************************)

let format_seqproof ff pf =
  let open Format in
  let rec spin ff pf =
    match pf with
    | InitL -> fprintf ff "InitL"
    | InitR h -> fprintf ff "InitR(%s)" h.rep
    | TensL (h1, h2, pf) -> fprintf ff "TensL(%s,%s,%a)" h1.rep h2.rep spin pf
    | TensR (pf1, pf2) -> fprintf ff "TensR(%a,%a)" spin pf1 spin pf2
    | OneR -> fprintf ff "OneR"
    | OneL pf -> fprintf ff "OneL(%a)" spin pf
    | PlusL (pf1, pf2) -> fprintf ff "PlusL(%a,%a)" spin1 pf1 spin1 pf2
    | PlusR1 pf -> fprintf ff "PlusR1(%a)" spin pf
    | PlusR2 pf -> fprintf ff "PlusR2(%a)" spin pf

    | ZeroL -> fprintf ff "ZeroL"

    | WithR (pf1, pf2) -> fprintf ff "WithR(%a,%a)" spin pf1 spin pf2
    | WithL1 pf -> fprintf ff "WithL1%a" spin1 pf
    | WithL2 pf -> fprintf ff "WithL2%a" spin1 pf

    | TopR -> fprintf ff "TopR"

    | ImpR (h, pf) -> fprintf ff "ImpR(%s,%a)" h.rep spin pf
    | ImpL (pf1, pf2) -> fprintf ff "ImpL(%a,%a)" spin pf1 spin1 pf2

    | AllR (x, pf) -> fprintf ff "ALlR(%s,%a)" x.rep spin pf
    | AllL (t, pf) -> fprintf ff "AllL(%a,%a)" (format_term ()) t spin1 pf

    | ExR (t, pf) -> fprintf ff "ExR(%a,%a)" (format_term ()) t spin pf
    | ExL (x, pf) -> fprintf ff "ExL(%s,%a)" x.rep spin1 pf

    | FocR pf -> fprintf ff "FocR(%a)" spin pf
    | FocL (x, pf) -> fprintf ff "FocL(%s,%a)" x.rep spin1 pf

    | BlurR pf -> fprintf ff "BlurR(%a)" spin pf
    | BlurL pf -> fprintf ff "BlurL(%a)" spin pf

    | Store (h, pf) -> fprintf ff "Store(%s,%a)" h.rep spin pf

  and spin1 ff (x, pf) =
    fprintf ff "@[<b1>(%s,@,%a)@]" x.rep spin pf

  in
  spin ff pf


(******************************************************************************)

type sequent = {
  term_vars    : Nstore.t ;
  left_passive : (idt * form) IdtMap.t ;
  left_active  : (idt * form) list ;
  right        : form ;
}

let replace_sequent ~repl sq =
  let left_passive = IdtMap.map begin
      fun (l, f) -> (l, Form.replace ~repl f)
    end sq.left_passive in
  let left_active = List.map begin
      fun (x, f) -> (x, Form.replace ~repl f)
    end sq.left_active in
  let right = Form.replace ~repl sq.right in
  {sq with left_passive ; left_active ; right}

let fresh_eig_for sq x =
  let x = match x.rep.[0] with
    | '$' -> x
    | _ -> intern @@ "$" ^ x.rep
  in
  let (term_vars, x) = Nstore.fresh_wrt sq.term_vars x in
  let sq = {sq with term_vars} in
  (sq, Term.app x [])

let hypgen = new Namegen.namegen
  (fun n -> intern @@ "u" ^ string_of_int n)

let format_sequent fmt sq =
  let open Format in
  pp_open_box fmt 0 ; begin
    begin match IdtMap.pop sq.left_passive with
    | (x, (l, f)), left ->
        (* pp_print_string fmt (x.Idt.rep ^ "[" ^ l.Idt.rep ^ "]") ; *)
        pp_print_string fmt x.Idt.rep ;
        pp_print_string fmt ":" ;
        format_form () fmt f ;
        IdtMap.iter begin
          fun x (l, f) ->
            pp_print_string fmt "," ;
            pp_print_space fmt () ;
            (* pp_print_string fmt (x.Idt.rep ^ "[" ^ l.Idt.rep ^ "]") ; *)
            pp_print_string fmt x.Idt.rep ;
            pp_print_string fmt ":" ;
            format_form () fmt f ;
        end left
    | exception Not_found ->
        pp_print_as fmt 1 "·"
    end ;
    pp_print_string fmt " ;" ;
    pp_print_space fmt () ;
    begin match sq.left_active with
    | [] -> pp_print_as fmt 1 "·"
    | (x, f) :: left ->
        pp_print_string fmt x.Idt.rep ;
        pp_print_string fmt ":" ;
        format_form () fmt f ;
        List.iter begin
          fun (x, f) ->
            pp_print_string fmt "," ;
            pp_print_space fmt () ;
            pp_print_string fmt x.Idt.rep ;
            pp_print_string fmt ":" ;
            format_form () fmt f ;
        end left
    end ;
    pp_print_as fmt 2 " ⊢" ;
    pp_print_space fmt () ;
    format_form () fmt sq.right ;
  end ; pp_close_box fmt ()
