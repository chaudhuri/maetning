(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014  INRIA (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Idt
open Term

exception Unif of string
let unifwithf fmt = Printf.ksprintf (fun s -> raise @@ Unif s) fmt

let compatible v t =
  match v.rep.[0] with
  | '?' -> true
  | '\'' -> begin
      match t.term with
      | Var w when w.rep.[0] == '\'' -> true
      | _ -> false
    end
  | _ -> failwith "bad variable"

let join ?depth ss v t =
  let vtss = IdtMap.digest [v, t] in
  let ss = IdtMap.map (replace ?depth ~repl:vtss) ss in
  IdtMap.insert ss v t

let rec unite ?depth ss t1 t2 =
  if t1 = t2 then (ss, t1) else
  match t1.term, t2.term with
  | Var v1, _ when IdtMap.mem v1 ss ->
      unite ?depth ss (IdtMap.find v1 ss) t2
  | Var v1, _ ->
      if IdtSet.mem v1 t2.vars then unifwithf "occur check" ;
      if not @@ compatible v1 t2 then unifwithf "variable incompatibility" ;
      let t = replace ?depth ~repl:ss t2 in
      (join ?depth ss v1 t, t)
  | _, Var v2 ->
      unite ?depth ss t2 t1
  | App (f1 as f, ts1), App (f2, ts2) when f1 == f2 ->
      let (ss, ts) = unite_lists ?depth ss ts1 ts2 in
      (ss, app f ts)
  | App (f1, _), App (f2, _) ->
      unifwithf "function-function: %s != %s" f1.rep f2.rep
  | Idx m, Idx n ->
      assert (m != n) ;
      unifwithf "index-index: %d != %d" m n
  | Idx _, App _
  | App _, Idx _  ->
      unifwithf "incompatible structures"

and unite_lists ?depth ss ts1 ts2 =
  match ts1, ts2 with
  | [], [] -> (ss, [])
  | (t1 :: ts1), (t2 :: ts2) ->
      let (ss, t) = unite ?depth ss t1 t2 in
      let (ss, ts) = unite_lists ?depth ss ts1 ts2 in
      (ss, t :: ts)
  | _ -> unifwithf "argument lists not the same length"

module Tests = struct
  let (f, g, h) = (intern "f", intern "g", intern "h")
  let (x, y, z) = (intern "?X", intern "?Y", intern "?Z")
  let (a, b, c) = (intern "'a", intern "'b", intern "'c")
  let t1 = app f [var x ; app g [var y ; var x]]
  let t2 = app f [app h [var y] ; var z]
  let run () =
    let (ss, t) = unite IdtMap.empty t1 t2 in
    print_endline @@ term_to_string (replace ~repl:ss t1) ;
    print_endline @@ term_to_string (replace ~repl:ss t2) ;
    print_endline @@ term_to_string t
end
