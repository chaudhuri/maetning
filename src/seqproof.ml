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

type proof =
  | InitL
  | InitR  of idt

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
  | ImpR   of idt * proof

  | AllL   of term * proof1
  | AllR   of idt * proof

  | ExL    of idt * proof1
  | ExR    of term * proof

  | FocR   of proof
  | FocL   of idt * proof1

  | BlurR  of proof
  | BlurL  of proof

  | Store  of proof1

and proof1 = idt * proof
and proof2 = idt * idt * proof

type sequent = {
  term_vars    : IdtSet.t ;
  left_passive : (idt * form) list ;
  left_active  : (idt * form) list ;
  right        : form ;
}

let replace_zone ~repl zone =
  List.map begin
    fun (x, f) -> (x, Form.replace ~repl f)
  end zone

let replace_sequent ~repl sq =
  let left_passive = replace_zone ~repl sq.left_passive in
  let left_active = replace_zone ~repl sq.left_active in
  let right = Form.replace ~repl sq.right in
  {sq with left_passive ; left_active ; right}

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

type 'a result =
  | Choices of 'a list
  | Invalid of string

type ('cert, 'a) op = sequent -> 'cert -> 'a result

module type AGENCY = sig
  type cert

  val ex_InitR  : (cert, int) op
  val ex_InitL  : (cert, 'a) op

  val cl_TensL  : (cert, idt * idt * cert) op
  val ex_TensR  : (cert, cert * cert) op

  val cl_OneL   : (cert, cert) op
  val ex_OneR   : (cert, 'a) op

  val cl_PlusL  : (cert, (idt * cert) * (idt * cert)) op
  val ex_PlusR  : (cert, [`left | `right] * cert) op

  val cl_ZeroL  : (cert, 'a) op

  val ex_WithL  : (cert, [`left | `right] * (idt * cert)) op
  val cl_WithR  : (cert, cert * cert) op

  val cl_TopR   : (cert, 'a) op

  val ex_ImpL   : (cert, cert * (idt * cert)) op
  val cl_ImpR   : (cert, idt * cert) op

  val ex_AllL   : (cert, term * (idt * cert)) op
  val cl_AllR   : (cert, term * cert) op

  val cl_ExL    : (cert, term * (idt * cert)) op
  val ex_ExR    : (cert, term * cert) op

  val ex_BlurR  : (cert, cert) op
  val ex_BlurL  : (cert, cert) op

  val cl_Store  : (cert, idt * cert) op
  val ex_Foc    : (cert, [`right of cert | `left of idt * (idt * cert)]) op
end

let unconst t =
  match t.term with
  | App (f, []) -> f
  | _ -> failwith "unconst"

exception Occurs

(* [TODO] term hashconsing will make this faster *)
let rec contains_term small big =
  big = small || begin
    match big.term with
    | Var _ | Idx _ -> false
    | App (_, ts) ->
        List.exists (contains_term small) ts
  end

let evc u repl =
  IdtMap.iter begin
    fun _ t ->
      if contains_term u t then raise Occurs
  end repl

let rec backtrack ~cc ~fail fn =
  match cc with
  | Invalid msg -> fail msg
  | Choices [] -> failwith "Invalid call to backtrack"
  | Choices [c] -> fn c ~fail
  | Choices (c :: cs) ->
      fn c ~fail:(fun _ -> backtrack ~cc:(Choices cs) ~fail fn)

let reconstruct (type cert)
    (module Ag : AGENCY with type cert = cert)
    ~goal ~(cert:cert) =

  let rec right_focus ~succ ~fail sq c =
    assert (List.length sq.left_active = 0) ;
    match sq.right.form with
    | Atom (POS, p, pts) ->
        backtrack ~cc:(Ag.ex_InitR sq c) ~fail begin
          fun n ~fail ->
            match List.nth sq.left_passive n with
            | (x, {form = Atom (POS, q, qts) ; _}) when p == q -> begin
                match Unify.unite_lists IdtMap.empty pts qts with
                | (repl, _) -> succ (InitR x, repl)
                | exception Unify.Unif _ -> fail "InitR/unify"
              end
            | _ -> fail "InitR/incompat"
        end
    | And (POS, a, b) ->
        backtrack ~cc:(Ag.ex_TensR sq c) ~fail begin
          fun (c1, c2) ~fail ->
            right_focus {sq with right = a} c1
              ~fail
              ~succ:begin fun (lder, repl) ->
                let sq = replace_sequent ~repl {sq with right = b} in
                right_focus sq c2 ~fail
                  ~succ:(fun (rder, repl) ->
                      let lder = replace_proof ~repl lder in
                      succ (TensR (lder, rder), repl))
              end
        end
    | True POS -> begin
        match Ag.ex_OneR sq c with
        | Choices [] -> succ (OneR, IdtMap.empty)
        | Choices _ -> failwith "OneR expert is bad"
        | Invalid msg -> fail msg
      end
    | Or (a, b) ->
        backtrack ~cc:(Ag.ex_PlusR sq c) ~fail begin
          fun (lr, c) ~fail ->
            let ab, dfn = match lr with
              | `left -> (a, fun d -> PlusR1 d)
              | `right -> (b, fun d -> PlusR2 d)
            in
            right_focus {sq with right = ab} c
              ~succ:(fun (der, repl) -> succ (dfn der, repl))
              ~fail
        end
    | Exists (x, a) ->
        backtrack ~cc:(Ag.ex_ExR sq c) ~fail begin
          fun (t, c) ~fail ->
            let right = app_form (Cons (Shift 0, t)) a in
            let sq = {sq with right} in
            right_focus sq c ~fail
              ~succ:(fun (der, repl) ->
                  let tt = Term.replace ~repl t in
                  let repl = IdtMap.remove (Term.unvar t) repl in
                  succ (ExR (tt, der), repl))
        end
    | False ->
        fail "FalseR"
    | Shift a ->
        backtrack ~cc:(Ag.ex_BlurR sq c) ~fail begin
          fun c ~fail ->
            right_active sq c ~fail
              ~succ:(fun (der, repl) -> succ (BlurR der, repl))
        end
    | Atom (NEG, _, _)
    | And (NEG, _, _) | True NEG | Implies _ | Forall _ ->
        failwith "right focus on active formula"

  and left_focus ~succ ~fail sq c =
    match sq.left_active with
    | [_, {form = Atom (NEG, p, pts) ; _}] -> begin
        match Ag.ex_InitL sq c with
        | Choices [] -> begin
            match sq.right.form with
            | Atom (NEG, q, qts) when p == q -> begin
                match Unify.unite_lists IdtMap.empty pts qts with
                | (repl, _) -> succ (InitL, repl)
                | exception Unify.Unif _ -> fail "InitL/unify"
              end
            | _ -> fail "InitL/incompat"
          end
        | Choices _ -> failwith "InitL expert is bad"
        | Invalid msg -> fail msg
      end
    | [_, {form = And (NEG, a, b) ; _}] ->
        backtrack ~cc:(Ag.ex_WithL sq c) ~fail begin
          fun (lr, (y, c)) ~fail ->
            let ab, dfn = match lr with
              | `left -> (a, fun d -> WithL1 (y, d))
              | `right -> (b, fun d -> WithL2 (y, d))
            in
            let sq = {sq with left_active = [(y, ab)]} in
            left_focus sq c ~fail
              ~succ:(fun (der, repl) -> succ (dfn der, repl))
        end
    | [_, {form = True NEG ; _}] ->
        fail "TopL"
    | [_, {form = Implies (a, b) ; _}] ->
        backtrack ~cc:(Ag.ex_ImpL sq c) ~fail begin
          fun (ca, (y, cb)) ~fail ->
            right_focus {sq with left_active = [] ; right = a} ca
              ~fail
              ~succ:begin fun (dera, repl) ->
                let sq = {sq with left_active = [y, b]} in
                let sq = replace_sequent ~repl sq in
                left_focus sq cb ~fail
                  ~succ:begin fun (derb, repl) ->
                    let dera = replace_proof ~repl dera in
                    succ (ImpL (dera, (y, derb)), repl)
                  end
              end
        end
    | [_, {form = Forall (x, a) ; _}] ->
        backtrack ~cc:(Ag.ex_AllL sq c) ~fail begin
          fun (t, (y, c)) ~fail ->
            let a = app_form (Cons (Shift 0, t)) a in
            let sq = {sq with left_active = [y, a]} in
            left_focus sq c ~fail
              ~succ:begin fun (der, repl) ->
                let tt = Term.replace ~repl t in
                let repl = IdtMap.remove (Term.unvar t) repl in
                succ (AllL (tt, (y, der)), repl)
              end
        end
    | [_, {form = Shift a ; _}] ->
        backtrack ~cc:(Ag.ex_BlurL sq c) ~fail begin
          fun c ~fail ->
            left_active sq c ~fail
              ~succ:(fun (der, repl) -> succ (BlurL der, repl))
        end
    | [_, {form = ( Atom (POS, _, _) | And (POS, _, _) | True POS
                  | Or _ | False | Exists _ ) ; _}] ->
        failwith "left focus on positive formula"
    | [] | _ :: _ ->
        failwith "left focus requires singleton focus"

  and right_active ~succ ~fail sq c =
    match sq.right.form with
    | Atom (NEG, _, _) ->
        (* silent handoff *)
        left_active ~succ ~fail sq c
    | Shift a ->
        let sq = {sq with right = a} in
        (* silent handoff *)
        left_active ~succ ~fail sq c
    | And (NEG, a, b) ->
        backtrack ~cc:(Ag.cl_WithR sq c) ~fail begin
          fun (ca, cb) ~fail ->
            right_active {sq with right = a} ca ~fail
              ~succ:begin fun (dera, repl) ->
                let sq = {sq with right = b}
                         |> replace_sequent ~repl in
                right_active sq cb ~fail
                  ~succ:begin fun (derb, repl) ->
                    let dera = replace_proof ~repl dera in
                    succ (WithR (dera, derb), repl)
                  end
              end
        end
    | True NEG -> begin
        match Ag.cl_TopR sq c with
        | Choices [] -> succ (TopR, IdtMap.empty)
        | Choices _ -> failwith "TopR expert is bad"
        | Invalid msg -> fail msg
      end
    | Implies (a, b) ->
        backtrack ~cc:(Ag.cl_ImpR sq c) ~fail begin
          fun (x, c) ~fail ->
            let sq = {sq with left_active = (x, a) :: sq.left_active ;
                              right = b} in
            right_active sq c ~fail
              ~succ:(fun (der, repl) -> succ (ImpR (x, der), repl))
        end
    | Forall (x, a) ->
        backtrack ~cc:(Ag.cl_AllR sq c) ~fail begin
          fun (u, c) ~fail ->
            (* [TODO] need to check that u is really a fresh param *)
            let right = app_form (Cons (Shift 0, u)) a in
            let term_vars = IdtSet.add (unconst u) sq.term_vars in
            let sq = {sq with term_vars ; right} in
            right_active sq c ~fail
              ~succ:begin fun (der, repl) ->
                match evc u repl with
                | () -> succ (AllR (unconst u, der), repl)
                | exception Occurs -> fail "AllR/evc"
              end
        end
    | Atom (POS, _, _) | And (POS, _, _) | True POS
    | Or _ | False | Exists _ ->
        failwith "right active on positive formula"

  and left_active ~succ ~fail sq c =
    match sq.left_active with
    | [] -> frontier ~succ ~fail sq c
    | (_, f0) :: rest -> begin
        match f0.form with
        | Atom (POS, _, _) ->
            backtrack ~cc:(Ag.cl_Store sq c) ~fail begin
              fun (x, c) ~fail ->
                let sq = {sq with left_active = rest ;
                                  left_passive = (x, f0) :: sq.left_passive} in
                left_active sq c ~fail
                  ~succ:(fun (der, repl) -> succ (Store (x, der), repl))
            end
        | Shift a ->
            backtrack ~cc:(Ag.cl_Store sq c) ~fail begin
              fun (x, c) ~fail ->
                let sq = {sq with left_active = rest ;
                                  left_passive = (x, a) :: sq.left_passive} in
                left_active sq c ~fail
                  ~succ:(fun (der, repl) -> succ (Store (x, der), repl))
            end
        | And (POS, a, b) ->
            backtrack ~cc:(Ag.cl_TensL sq c) ~fail begin
              fun (x, y, c) ~fail ->
                let sq = {sq with left_active = (x, a) :: (y, b) :: rest} in
                left_active sq c ~fail
                  ~succ:(fun (der, repl) -> succ (TensL (x, y, der), repl))
            end
        | True POS ->
            backtrack ~cc:(Ag.cl_OneL sq c) ~fail begin
              fun c ~fail ->
                let sq = {sq with left_active = rest} in
                left_active sq c ~fail
                  ~succ:(fun (der, repl) -> succ (OneL der, repl))
            end
        | Or (a, b) ->
            backtrack ~cc:(Ag.cl_PlusL sq c) ~fail begin
              fun ((xa, ca), (xb, cb)) ~fail ->
                let sqa = {sq with left_active = (xa, a) :: rest} in
                left_active sqa ca ~fail
                  ~succ:begin fun (dera, repl) ->
                    let sqb = {sq with left_active = (xb, b) :: rest}
                              |> replace_sequent ~repl in
                    left_active sqb cb ~fail
                      ~succ:begin fun (derb, repl) ->
                        let dera = replace_proof ~repl dera in
                        succ (PlusL ((xa, dera), (xb, derb)), repl)
                      end
                  end
            end
        | False -> begin
            match Ag.cl_ZeroL sq c with
            | Choices [] -> succ (ZeroL, IdtMap.empty)
            | Choices _ -> failwith "ZeroL expert is broken"
            | Invalid msg -> fail msg
          end
        | Exists (x, a) ->
            backtrack ~cc:(Ag.cl_ExL sq c) ~fail begin
              fun (u, (xx, c)) ~fail ->
                let a = app_form (Cons (Shift 0, u)) a in
                let sq = {sq with left_active = (xx, a) :: rest} in
                left_active sq c ~fail
                  ~succ:begin fun (der, repl) ->
                    match evc u repl with
                    | () -> succ (ExL (unconst u, (xx, der)), repl)
                    | exception Occurs -> fail "ExL/evc"
                  end
            end
        | Atom (NEG, _, _) | And (NEG, _, _) | True NEG
        | Implies _ | Forall _ ->
            failwith "right active on negative formula"
      end

  and frontier ~succ ~fail sq c =
    backtrack ~cc:(Ag.ex_Foc sq c) ~fail begin
      fun instr ~fail -> match instr with
        | `right c ->
            right_focus sq c ~fail
              ~succ:(fun (der, repl) -> succ (FocR der, repl))
        | `left (x, (xx, c)) -> begin
            match List.assoc x sq.left_passive with
            | a when polarity a = NEG ->
                let sq = {sq with left_active = [(xx, a)]} in
                left_focus sq c ~fail
                  ~succ:(fun (der, repl) -> succ (FocL (x, (xx, der)), repl))
            | _ -> fail "FocL/nonpos"
            | exception Not_found -> failwith "Foc expert is broken"
          end
    end
  in
  frontier goal cert
    ~succ:(fun (der, _) -> Some der)
    ~fail:begin fun msg ->
      Format.eprintf "reconstruct: %s@." msg ;
      None
    end
