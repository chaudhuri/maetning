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

type 'a result =
  | Choices of 'a list
  | Invalid of string

type ('cert, 'a) op = sequent -> 'cert -> 'a result

module type AGENCY = sig
  type cert
  val format_cert : Format.formatter -> cert -> unit

  (* Experts are named ex_ *)
  (* Clerks  are named cl_ *)

  val ex_InitR  : (cert, hyp) op
  val ex_InitL  : (cert, 'a) op

  val cl_TensL  : (cert, hyp -> hyp -> cert) op
  val ex_TensR  : (cert, cert * cert) op

  val cl_OneL   : (cert, cert) op
  val ex_OneR   : (cert, 'a) op

  val cl_PlusL  : (cert, (hyp -> cert) * (hyp -> cert)) op
  val ex_PlusR  : (cert, [`left | `right] * cert) op

  val cl_ZeroL  : (cert, 'a) op

  val ex_WithL  : (cert, [`left | `right] * (hyp -> cert)) op
  val cl_WithR  : (cert, cert * cert) op

  val cl_TopR   : (cert, 'a) op

  val ex_ImpL   : (cert, cert * (hyp -> cert)) op
  val cl_ImpR   : (cert, hyp -> cert) op

  val ex_AllL   : (cert, term * (hyp -> cert)) op
  val cl_AllR   : (cert, term -> cert) op

  val cl_ExL    : (cert, term -> (hyp -> cert)) op
  val ex_ExR    : (cert, term * cert) op

  val ex_BlurR  : (cert, cert) op
  val ex_BlurL  : (cert, cert) op

  val cl_Store  : (cert, hyp -> cert) op
  val ex_Foc    : (cert, [`right of cert | `left of hyp * (hyp -> cert)]) op
end

(******************************************************************************)

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
  | Invalid msg -> fail ("Invalid: " ^ msg)
  | Choices [] -> failwith "Invalid call to backtrack"
  | Choices [c] -> fn c ~fail
  | Choices (c :: cs) ->
      fn c ~fail:(fun _ -> backtrack ~cc:(Choices cs) ~fail fn)

let __debug = false

let reconstruct (type cert)
    (module Ag : AGENCY with type cert = cert)
    ~lforms ~goal ~(cert:cert) =

  assert (goal.left_active = [] && polarity goal.right = POS) ;

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

  let goal = {goal with left_passive = List.map expand_lf2 goal.left_passive ;
                        right = expand_lf goal.right}
  in

  let rec right_focus ~succ ~fail sq c =
    assert (List.length sq.left_active = 0) ;
    Format.(
      if __debug then
        fprintf std_formatter "right_focus: %a@.  %a@."
          format_sequent sq Ag.format_cert c
    ) ;
    match sq.right.form with
    | Atom (POS, p, pts) ->
        backtrack ~cc:(Ag.ex_InitR sq c) ~fail begin
          fun x ~fail ->
            match (snd @@ List.assoc x sq.left_passive).form with
            | Atom (POS, q, qts) when p == q -> begin
                match Unify.unite_lists IdtMap.empty pts qts with
                | (repl, _) -> succ (InitR x, repl)
                | exception Unify.Unif _ -> fail "InitR/unify"
              end
            | _ -> fail "InitR/incompat"
            | exception Not_found -> failwith "InitR expert is bad"
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
    | False ->
        fail "FalseR"
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
    | Shift a ->
        backtrack ~cc:(Ag.ex_BlurR sq c) ~fail begin
          fun c ~fail ->
            let sq = {sq with right = a} in
            right_active sq c ~fail
              ~succ:(fun (der, repl) -> succ (BlurR der, repl))
        end
    | Atom (NEG, _, _)
    | And (NEG, _, _) | True NEG | Implies _ | Forall _ ->
        failwith "right focus on active formula"

  and left_focus ~succ ~fail sq c =
    Format.(
      if __debug then
        fprintf std_formatter "left_focus: %a@.  %a@."
          format_sequent sq Ag.format_cert c
    ) ;
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
          fun (lr, cfn) ~fail ->
            let y = hypgen#next in
            let c = cfn y in
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
          fun (ca, cbfn) ~fail ->
            let y = hypgen#next in
            let cb = cbfn y in
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
          fun (t, cfn) ~fail ->
            let y = hypgen#next in
            let c = cfn y in
            let a = app_form (Cons (Shift 0, t)) a in
            let sq = {sq with left_active = [y, a]} in
            left_focus sq c ~fail
              ~succ:begin fun (der, repl) ->
                let tt = Term.replace ~repl t in
                let repl = IdtMap.remove (Term.unvar t) repl in
                succ (AllL (tt, (y, der)), repl)
              end
        end
    | [x, {form = Shift a ; _}] ->
        backtrack ~cc:(Ag.ex_BlurL sq c) ~fail begin
          fun c ~fail ->
            let sq = {sq with left_active = [x, a]} in
            left_active sq c ~fail
              ~succ:(fun (der, repl) -> succ (BlurL der, repl))
        end
    | [_, {form = ( Atom (POS, _, _) | And (POS, _, _) | True POS
                  | Or _ | False | Exists _ ) ; _}] ->
        failwith "left focus on positive formula"
    | [] | _ :: _ ->
        failwith "left focus requires singleton focus"

  and right_active ~succ ~fail sq c =
    Format.(
      if __debug then
        fprintf std_formatter "right_active: %a@.  %a@."
          format_sequent sq Ag.format_cert c
    ) ;
    match sq.right.form with
    | Atom (NEG, _, _) ->
        let sq = {sq with right = expand_lf sq.right} in
        (* silent Store *)
        left_active ~succ ~fail sq c
    | Shift a ->
        let sq = {sq with right = expand_lf a} in
        (* silent Store *)
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
          fun cfn ~fail ->
            let x = hypgen#next in
            let c = cfn x in
            let sq = {sq with left_active = (x, a) :: sq.left_active ;
                              right = b} in
            right_active sq c ~fail
              ~succ:(fun (der, repl) -> succ (ImpR (x, der), repl))
        end
    | Forall (x, a) ->
        backtrack ~cc:(Ag.cl_AllR sq c) ~fail begin
          fun cfn ~fail ->
            (* [TODO] need to check that u is really a fresh param *)
            let (sq, u) = fresh_eig_for sq x in
            let c = cfn u in
            let right = app_form (Cons (Shift 0, u)) a in
            let sq = {sq with right} in
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
    Format.(
      if __debug then
        fprintf std_formatter "left_active: %a@.  %a@."
          format_sequent sq Ag.format_cert c
    ) ;
    match sq.left_active with
    | [] -> frontier ~succ ~fail sq c
    | (_, f0) :: rest -> begin
        match f0.form with
        | Atom (POS, p, _) ->
            backtrack ~cc:(Ag.cl_Store sq c) ~fail begin
              fun cfn ~fail ->
                let x = hypgen#next in
                let c = cfn x in
                let sq = {sq with left_active = rest ;
                                  left_passive = (x, (p, expand_lf f0))
                                                 :: sq.left_passive} in
                left_active sq c ~fail
                  ~succ:(fun (der, repl) -> succ (Store (x, der), repl))
            end
        | Shift a ->
            let lab = match a.form with
              | Atom (NEG, lab, _) -> lab
              | _ -> failwith "labeling bug: label of stored formula unknown"
            in
            let a = expand_lf a in
            backtrack ~cc:(Ag.cl_Store sq c) ~fail begin
              fun cfn ~fail ->
                let x = hypgen#next in
                let c = cfn x in
                let sq = {sq with left_active = rest ;
                                  left_passive = (x, (lab, a)) :: sq.left_passive} in
                left_active sq c ~fail
                  ~succ:(fun (der, repl) -> succ (Store (x, der), repl))
            end
        | And (POS, a, b) ->
            backtrack ~cc:(Ag.cl_TensL sq c) ~fail begin
              fun cfn ~fail ->
                let x = hypgen#next in
                let y = hypgen#next in
                let c = cfn x y in
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
              fun (cafn, cbfn) ~fail ->
                let xa = hypgen#next in
                let ca = cafn xa in
                let xb = hypgen#next in
                let cb = cbfn xb in
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
            | Choices _ -> failwith "ZeroL expert is bad"
            | Invalid msg -> fail msg
          end
        | Exists (x, a) ->
            backtrack ~cc:(Ag.cl_ExL sq c) ~fail begin
              fun cfn ~fail ->
                let (sq, u) = fresh_eig_for sq x in
                let xx = hypgen#next in
                let c = cfn u xx in
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
            failwith "left active on negative formula"
      end

  and frontier ~succ ~fail sq c =
    Format.(
      if __debug then
        fprintf std_formatter "frontier: %a@.  %a@."
          format_sequent sq Ag.format_cert c ;
    ) ;
    backtrack ~cc:(Ag.ex_Foc sq c) ~fail begin
      fun instr ~fail -> match instr with
        | `right c ->
            right_focus sq c ~fail
              ~succ:(fun (der, repl) -> succ (FocR der, repl))
        | `left (x, cfn) -> begin
            let xx = hypgen#next in
            let c = cfn xx in
            match List.assoc x sq.left_passive with
            | (_, a) when polarity a = NEG ->
                let sq = {sq with left_active = [(xx, a)]} in
                left_focus sq c ~fail
                  ~succ:(fun (der, repl) -> succ (FocL (x, (xx, der)), repl))
            | _ -> fail "FocL/nonpos"
            | exception Not_found -> failwith "Foc expert is bad"
          end
    end
  in
  frontier goal cert
    ~succ:(fun (der, _) -> Some der)
    ~fail:begin fun msg ->
      Format.eprintf "reconstruct: %s@." msg ;
      None
    end

