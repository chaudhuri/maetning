(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries
open Debug

open Idt
open Term
open Form
open Seqproof

module M = VMap

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

let rec evc_term u t =
  match t.term with
  | Term.App (_, []) ->
      if u = t then raise Occurs
  | Term.App (_, ts) -> List.iter (evc_term u) ts
  | Var _ | Idx _ -> ()

let rec evc_form u f =
  match f.form with
  | Atom (_, _, ts) ->
      List.iter (evc_term u) ts
  | And (_, f, g) | Or (f, g) | Implies (f, g) ->
      evc_form u f ; evc_form u g
  | True _ | False -> ()
  | Exists (_, f) | Forall (_, f) | Shift f ->
      evc_form u f

let evc_sequent u sq =
  IdtMap.iter (fun _ (_, f) -> evc_form u f) sq.left_passive ;
  List.iter (fun (_, f) -> evc_form u f) sq.left_active ;
  evc_form u sq.right

let rec backtrack ~cc ~fail fn =
  match cc with
  | Invalid msg -> fail ("Invalid: " ^ msg)
  | Choices [] -> failwith "Invalid call to backtrack"
  | Choices [c] -> fn c ~fail
  | Choices (c :: cs) ->
      fn c ~fail:(fun reason ->
          dprintf "reconstruct" "Backtracking because %S@." reason ;
          backtrack ~cc:(Choices cs) ~fail fn
        )

let repl_join repl_left repl_right =
  M.merge begin fun k ts1 ts2 ->
    match ts1, ts2 with
    | Some ts1, Some ts2 ->
        Debug.failwithf "repl_join: overlap on %a" format_var k
    | Some ts, None -> Some (Term.replace ~repl:repl_right ts)
    | None, Some ts -> Some ts
    | None, None -> None
  end repl_left repl_right

let indent lev =
  String.make (2 * lev) ' '

let reconstruct (type cert)
    (module Ag : AGENCY with type cert = cert)
    ?(max=1) ~lforms ~goal ~(cert:cert) =

  if max <= 0 then Debug.bugf "reconstruct max = %d" max ;

  let expand_lf f = match f.form with
    | Atom (pol, p, ts) -> begin
        match IdtMap.find p lforms with
        | lf ->
            let ts = List.take (List.length lf.args) ts in
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

  let expand_lf2 (l, f) = (l, expand_lf f) in

  let goal = {goal with left_passive = IdtMap.map expand_lf2 goal.left_passive ;
                        right = expand_lf goal.right}
  in

  let rec right_focus lev ~succ ~fail sq c =
    if sq.left_active <> [] then Debug.bugf "right_focus: has left active" ;
    dprintf "reconstruct"
      "@.%s@[<v0>right_focus: @[%a@]@,  @[%a@]@]@."
      (indent lev)
      format_sequent sq Ag.format_cert c ;
    let lev = lev + 1 in
    match sq.right.form with
    | Atom (POS, p, pts) ->
        backtrack ~cc:(Ag.ex_InitR sq c) ~fail begin
          fun x ~fail ->
            match (snd @@ IdtMap.find x sq.left_passive).form with
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
            right_focus lev {sq with right = a} c1
              ~fail
              ~succ:begin fun (lder, lrepl) ~fail ->
                let sq = replace_sequent ~repl:lrepl {sq with right = b} in
                right_focus lev sq c2 ~fail
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
            right_focus lev {sq with right = ab} c
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
            right_focus lev sq c ~fail
              ~succ:(fun (der, repl) ~fail ->
                  let tt = Term.replace ~repl t in
                  let repl = M.remove (Term.unvar t) repl in
                  succ (ExR (tt, der), repl) ~fail)
        end
    | Shift a ->
        backtrack ~cc:(Ag.ex_BlurR sq c) ~fail begin
          fun c ~fail ->
            let sq = {sq with right = a} in
            right_active lev sq c ~fail
              ~succ:(fun (der, repl) ~fail -> succ (BlurR der, repl) ~fail)
        end
    | Atom (NEG, _, _)
    | And (NEG, _, _) | True NEG | Implies _ | Forall _ ->
        failwith "right focus on active formula"

  and left_focus lev ~succ ~fail sq c =
    dprintf "reconstruct"
      "@.%s@[<v0>left_focus: @[%a@]@,  @[%a@]@]@."
      (indent lev)
      format_sequent sq Ag.format_cert c ;
    let lev = lev + 1 in
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
            let sq = {sq with left_active = [y, ab]} in
            left_focus lev sq c ~fail
              ~succ:(fun (der, repl) ~fail -> succ (dfn der, repl) ~fail)
        end
    | [_, {form = True NEG ; _}] ->
        fail "TopL"
    | [_, {form = Implies (a, b) ; _}] ->
        backtrack ~cc:(Ag.ex_ImpL sq c) ~fail begin
          fun (ca, cbfn) ~fail ->
            let y = hypgen#next in
            let cb = cbfn y in
            right_focus lev {sq with left_active = [] ; right = a} ca
              ~fail
              ~succ:begin fun (dera, repla) ~fail ->
                let sq = {sq with left_active = [y, b]} in
                let sq = replace_sequent ~repl:repla sq in
                left_focus lev sq cb ~fail
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
            left_focus lev sq c ~fail
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
            left_active lev sq c ~fail
              ~succ:(fun (der, repl) ~fail -> succ (BlurL der, repl) ~fail)
        end
    | [_, {form = ( Atom (POS, _, _) | And (POS, _, _) | True POS
                  | Or _ | False | Exists _ ) ; _}] ->
        failwith "left focus on positive formula"
    | [] | _ :: _ ->
        failwith "left focus requires singleton focus"

  and right_active lev ~succ ~fail sq c =
    dprintf "reconstruct"
      "@.%s@[<v0>right_active: @[%a@]@,  @[%a@]@]@."
      (indent lev)
      format_sequent sq Ag.format_cert c ;
    let lev = lev + 1 in
    match sq.right.form with
    | Atom (NEG, _, _) ->
        let sq = {sq with right = expand_lf sq.right} in
        (* silent Store *)
        left_active lev ~succ ~fail sq c
    | Shift a ->
        let sq = {sq with right = expand_lf a} in
        (* silent Store *)
        left_active lev ~succ ~fail sq c
    | And (NEG, a, b) ->
        backtrack ~cc:(Ag.cl_WithR sq c) ~fail begin
          fun (ca, cb) ~fail ->
            right_active lev {sq with right = a} ca ~fail
              ~succ:begin fun (dera, repla) ~fail ->
                let sq = {sq with right = b}
                         |> replace_sequent ~repl:repla in
                right_active lev sq cb ~fail
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
            right_active lev sq c ~fail
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
            right_active lev sq c ~fail
              ~succ:begin fun (der, repl) ~fail ->
                let sq = {sq with right = abstract (unconst u) sq.right} in
                match evc_sequent u (Seqproof.replace_sequent ~repl sq) with
                | () -> succ (AllR (unconst u, der), repl) ~fail
                | exception Occurs ->
                    dprintf "reconstruct" "@.%s%a occurs in @[%a@]@."
                      (indent lev)
                      (format_term ()) u
                      Seqproof.format_sequent (Seqproof.replace_sequent ~repl sq) ;
                    fail "AllR/evc"
              end
        end
    | Atom (POS, _, _) | And (POS, _, _) | True POS
    | Or _ | False | Exists _ ->
        failwith "right active on positive formula"

  and left_active lev ~succ ~fail sq c =
    dprintf "reconstruct"
      "@.%s@[<v0>left_active: @[%a@]@,  @[%a@]@]@."
      (indent lev)
      format_sequent sq Ag.format_cert c ;
    let lev = lev + 1 in
    match sq.left_active with
    | [] -> frontier lev ~succ ~fail sq c
    | (u0, f0) :: rest -> begin
        match f0.form with
        | Atom (POS, p, _) ->
            backtrack ~cc:(Ag.cl_Store sq c) ~fail begin
              fun cfn ~fail ->
                let x = hypgen#next in
                let c = cfn x in
                let sq = {sq with left_active = rest ;
                                  left_passive = IdtMap.add x (p, expand_lf f0) sq.left_passive} in
                left_active lev sq c ~fail
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
                                  left_passive = IdtMap.add x (lab, a) sq.left_passive} in
                left_active lev sq c ~fail
                  ~succ:(fun (der, repl) ~fail -> succ (Store (x, der), repl) ~fail)
            end
        | And (POS, a, b) ->
            backtrack ~cc:(Ag.cl_TensL sq c) ~fail begin
              fun cfn ~fail ->
                let x = hypgen#next in
                let y = hypgen#next in
                let c = cfn x y in
                let sq = {sq with left_active = (x, a) :: (y, b) :: rest} in
                left_active lev sq c ~fail
                  ~succ:(fun (der, repl) ~fail -> succ (TensL (x, y, der), repl) ~fail)
            end
        | True POS ->
            backtrack ~cc:(Ag.cl_OneL sq c) ~fail begin
              fun c ~fail ->
                let sq = {sq with left_active = rest} in
                left_active lev sq c ~fail
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
                left_active lev sqa ca ~fail
                  ~succ:begin fun (dera, repla) ~fail ->
                    let sqb = {sq with left_active = (xb, b) :: rest}
                              |> replace_sequent ~repl:repla in
                    left_active lev sqb cb ~fail
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
                left_active lev sq c ~fail
                  ~succ:begin fun (der, repl) ~fail ->
                    let sq = {sq with left_active = (u0, abstract (unconst u) a) :: rest} in
                    let sq = Seqproof.replace_sequent ~repl sq in
                    match evc_sequent u sq with
                    | () -> succ (ExL (unconst u, (xx, der)), repl) ~fail
                    | exception Occurs ->
                        dprintf "reconstruct" "@.%s%a occurs in @[%a@]@."
                          (indent lev)
                          (format_term ()) u
                          Seqproof.format_sequent sq ;
                        fail "ExL/evc"
                  end
            end
        | Atom (NEG, _, _) | And (NEG, _, _) | True NEG
        | Implies _ | Forall _ ->
            failwith "left active on negative formula"
      end

  and frontier lev ~succ ~fail sq c =
    dprintf "reconstruct"
      "@.%s@[<v0>frontier: @[%a@]@,  @[%a@]@]@."
      (indent lev)
      format_sequent sq Ag.format_cert c ;
    let lev = lev + 1 in
    backtrack ~cc:(Ag.ex_Foc sq c) ~fail begin
      fun instr ~fail -> match instr with
        | `right c ->
            right_focus lev sq c ~fail
              ~succ:(fun (der, repl) ~fail -> succ (FocR der, repl) ~fail)
        | `left (x, cfn) -> begin
            dprintf "reconstruct" "Trying choice %s@." x.rep ;
            let xx = hypgen#next in
            let c = cfn xx in
            match IdtMap.find x sq.left_passive with
            | (_, a) when polarity a = NEG ->
                let sq = {sq with left_active = [xx, a]} in
                left_focus lev sq c ~fail
                  ~succ:(fun (der, repl) ~fail -> succ (FocL (x, (xx, der)), repl) ~fail)
            | _ -> fail "FocL/nonpos"
            | exception Not_found -> failwith "Foc expert is bad"
          end
    end
  in

  frontier 0 goal cert
    ~succ:(fun (der, _) ~fail -> Some der)
    ~fail:(fun msg ->
        Format.eprintf "reconstruct: %s@." msg ;
        None
      )
