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

module M = IdtMap

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
  M.iter begin
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

let format_repl ff repl =
  match M.bindings repl with
  | [] -> ()
  | (x, t) :: bs ->
      Format.(
        pp_open_box ff 1 ; begin
          fprintf ff "{%s:%a" x.rep (format_term ()) t ;
          List.iter begin fun (x, t) ->
            fprintf ff ",@,%s:%a" x.rep (format_term ()) t
          end bs ;
          pp_print_string ff "}" ;
        end ; pp_close_box ff ()
      )

let repl_join repl_left repl_right =
  M.merge begin fun k ts1 ts2 ->
    match ts1, ts2 with
    | Some ts1, Some ts2 ->
        failwith ("repl_join: overlap on " ^ k.rep)
    | Some ts, None
    | None, Some ts -> Some ts
    | None, None -> None
  end repl_left repl_right

let reconstruct (type cert)
    (module Ag : AGENCY with type cert = cert)
    ?(max=1) ~lforms ~goal ~(cert:cert) =

  assert (goal.left_active = [] && polarity goal.right = POS) ;
  assert (max > 0) ;

  let lf_dict = List.fold_left begin
      fun dict lf ->
        M.add lf.label lf dict
    end M.empty lforms in

  let expand_lf f = match f.form with
    | Atom (pol, p, ts) -> begin
        match M.find p lf_dict with
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
    let succ (pf, repl) ~fail =
      Format.(
        if __debug then
          fprintf std_formatter "  >>> right_focus: %a -->@.  >>> %a@."
            format_sequent sq
            format_repl repl
      ) ;
      succ (pf, repl) ~fail
    in
    match sq.right.form with
    | Atom (POS, p, pts) ->
        backtrack ~cc:(Ag.ex_InitR sq c) ~fail begin
          fun x ~fail ->
            match (snd @@ List.assoc x sq.left_passive).form with
            | Atom (POS, q, qts) when p == q -> begin
                match Unify.unite_lists M.empty pts qts with
                | (repl, _) -> succ (InitR x, repl) ~fail
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
              ~succ:begin fun (lder, lrepl) ~fail ->
                let sq = replace_sequent ~repl:lrepl {sq with right = b} in
                right_focus sq c2 ~fail
                  ~succ:(fun (rder, rrepl) ~fail ->
                      let lder = replace_proof ~repl:rrepl lder in
                      succ (TensR (lder, rder), repl_join lrepl rrepl) ~fail)
              end
        end
    | True POS -> begin
        match Ag.ex_OneR sq c with
        | Choices [] -> succ (OneR, M.empty) ~fail
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
              ~succ:(fun (der, repl) ~fail -> succ (dfn der, repl) ~fail)
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
              ~succ:(fun (der, repl) ~fail ->
                  let tt = Term.replace ~repl t in
                  let repl = M.remove (Term.unvar t) repl in
                  succ (ExR (tt, der), repl) ~fail)
        end
    | Shift a ->
        backtrack ~cc:(Ag.ex_BlurR sq c) ~fail begin
          fun c ~fail ->
            let sq = {sq with right = a} in
            right_active sq c ~fail
              ~succ:(fun (der, repl) ~fail -> succ (BlurR der, repl) ~fail)
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
                match Unify.unite_lists M.empty pts qts with
                | (repl, _) -> succ (InitL, repl) ~fail
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
              ~succ:(fun (der, repl) ~fail -> succ (dfn der, repl) ~fail)
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
              ~succ:begin fun (dera, repla) ~fail ->
                let sq = {sq with left_active = [y, b]} in
                let sq = replace_sequent ~repl:repla sq in
                left_focus sq cb ~fail
                  ~succ:begin fun (derb, replb) ~fail ->
                    let dera = replace_proof ~repl:replb dera in
                    succ (ImpL (dera, (y, derb)), repl_join repla replb) ~fail
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
              ~succ:begin fun (der, repl) ~fail ->
                let tt = Term.replace ~repl t in
                let repl = M.remove (Term.unvar t) repl in
                succ (AllL (tt, (y, der)), repl) ~fail
              end
        end
    | [x, {form = Shift a ; _}] ->
        backtrack ~cc:(Ag.ex_BlurL sq c) ~fail begin
          fun c ~fail ->
            let sq = {sq with left_active = [x, a]} in
            left_active sq c ~fail
              ~succ:(fun (der, repl) ~fail -> succ (BlurL der, repl) ~fail)
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
              ~succ:begin fun (dera, repla) ~fail ->
                let sq = {sq with right = b}
                         |> replace_sequent ~repl:repla in
                right_active sq cb ~fail
                  ~succ:begin fun (derb, replb) ~fail ->
                    let dera = replace_proof ~repl:replb dera in
                    succ (WithR (dera, derb), repl_join repla replb) ~fail
                  end
              end
        end
    | True NEG -> begin
        match Ag.cl_TopR sq c with
        | Choices [] -> succ (TopR, M.empty) ~fail
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
              ~succ:(fun (der, repl) ~fail -> succ (ImpR (x, der), repl) ~fail)
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
              ~succ:begin fun (der, repl) ~fail ->
                match evc u repl with
                | () -> succ (AllR (unconst u, der), repl) ~fail
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
                  ~succ:(fun (der, repl) ~fail -> succ (Store (x, der), repl) ~fail)
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
                  ~succ:(fun (der, repl) ~fail -> succ (Store (x, der), repl) ~fail)
            end
        | And (POS, a, b) ->
            backtrack ~cc:(Ag.cl_TensL sq c) ~fail begin
              fun cfn ~fail ->
                let x = hypgen#next in
                let y = hypgen#next in
                let c = cfn x y in
                let sq = {sq with left_active = (x, a) :: (y, b) :: rest} in
                left_active sq c ~fail
                  ~succ:(fun (der, repl) ~fail -> succ (TensL (x, y, der), repl) ~fail)
            end
        | True POS ->
            backtrack ~cc:(Ag.cl_OneL sq c) ~fail begin
              fun c ~fail ->
                let sq = {sq with left_active = rest} in
                left_active sq c ~fail
                  ~succ:(fun (der, repl) ~fail -> succ (OneL der, repl) ~fail)
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
                  ~succ:begin fun (dera, repla) ~fail ->
                    let sqb = {sq with left_active = (xb, b) :: rest}
                              |> replace_sequent ~repl:repla in
                    left_active sqb cb ~fail
                      ~succ:begin fun (derb, replb) ~fail ->
                        let dera = replace_proof ~repl:replb dera in
                        succ (PlusL ((xa, dera), (xb, derb)), repl_join repla replb) ~fail
                      end
                  end
            end
        | False -> begin
            match Ag.cl_ZeroL sq c with
            | Choices [] -> succ (ZeroL, M.empty) ~fail
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
                  ~succ:begin fun (der, repl) ~fail ->
                    match evc u repl with
                    | () -> succ (ExL (unconst u, (xx, der)), repl) ~fail
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
              ~succ:(fun (der, repl) ~fail -> succ (FocR der, repl) ~fail)
        | `left (x, cfn) -> begin
            let xx = hypgen#next in
            let c = cfn xx in
            match List.assoc x sq.left_passive with
            | (_, a) when polarity a = NEG ->
                let sq = {sq with left_active = [(xx, a)]} in
                left_focus sq c ~fail
                  ~succ:(fun (der, repl) ~fail -> succ (FocL (x, (xx, der)), repl) ~fail)
            | _ -> fail "FocL/nonpos"
            | exception Not_found -> failwith "Foc expert is bad"
          end
    end
  in
  let proofs = ref [] in
  let nproofs = ref 0 in

  frontier goal cert
    ~succ:(fun (der, _) ~fail ->
        if !nproofs < max then begin
          incr nproofs ;
          proofs := der :: !proofs ;
          fail "next proof"
        end else Some !proofs)
    ~fail:begin fun msg ->
      match !proofs with
      | [] ->
          Format.eprintf "reconstruct: %s@." msg ;
          None
      | pfs -> Some pfs
    end
