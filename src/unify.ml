(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014,2015  Inria
 *     (Institut National de Recherche en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Idt
open Term

exception Unif of string
let unif_fail fmt = Printf.ksprintf (fun s -> raise @@ Unif s) fmt

let compatible v t =
  match v.rep.[0] with
  | '?' -> true
  | '\'' -> begin
      match t.term with
      | Var w when w.rep.[0] == '\'' -> true
      | _ -> false
    end
  | _ -> failwith "bad variable"

let is_evar v = v.rep.[0] == Term.evar_cookie.[0]
let is_evar_term t =
  match t.term with
  | Var v -> is_evar v
  | _ -> false

let is_param v = v.rep.[0] == Term.param_cookie.[0]
let is_param_term t =
  match t.term with
  | Var v -> is_param v
  | _ -> false

let rec vnorm ss t =
  match t.term with
  | Var v when IdtMap.mem v ss ->
      vnorm ss (IdtMap.find v ss)
  | _ -> t

let rec unite ?depth ?(frz=IdtSet.empty) ss t1 t2 =
  let t1 = vnorm ss t1 in
  let t2 = vnorm ss t2 in
  if t1 = t2 then (ss, t1) else
  match t1.term, t2.term with
  | Var v1, Var v2 when is_param v1 && is_evar v2 ->
      unite ?depth ~frz ss t2 t1
  | Var v1, _ ->
      if IdtSet.mem v1 t2.vars then unif_fail "occur check" ;
      if not @@ compatible v1 t2 then unif_fail "variable incompatibility" ;
      if IdtSet.mem v1 frz then unif_fail "frozen variable" ;
      let t = replace ?depth ~repl:ss t2 in
      (join ?depth ss v1 t, t)
  | _, Var v2 ->
      unite ?depth ~frz ss t2 t1
  | App (f1 as f, ts1), App (f2, ts2) when f1 == f2 ->
      let (ss, ts) = unite_lists ?depth ~frz ss ts1 ts2 in
      (ss, app f ts)
  | App (f1, _), App (f2, _) ->
      unif_fail "function-function: %s != %s" f1.rep f2.rep
  | Idx m, Idx n ->
      assert (m != n) ;
      unif_fail "index-index: %d != %d" m n
  | Idx _, App _
  | App _, Idx _  ->
      unif_fail "incompatible structures"

and unite_lists ?depth ?frz ss ts1 ts2 =
  match ts1, ts2 with
  | [], [] -> (ss, [])
  | (t1 :: ts1), (t2 :: ts2) ->
      let (ss, t) = unite ?depth ?frz ss t1 t2 in
      let (ss, ts) = unite_lists ?depth ?frz ss ts1 ts2 in
      (ss, t :: ts)
  | _ -> unif_fail "argument lists not the same length"

let unite_match ?depth ss t1 t2 =
  let frz = freeze_term t2 in
  unite ?depth ~frz ss t1 t2

let unite_match_lists ?depth ss ts1 ts2 =
  let frz = freeze_terms ts2 in
  unite_lists ?depth ~frz ss ts1 ts2
