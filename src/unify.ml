(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014,2015  Inria
 *     (Institut National de Recherche en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Idt
open Term

exception Unif of string

let unif_fail fmt =
  let open Format in
  let buf = Buffer.create 19 in
  let ff = formatter_of_buffer buf in
  kfprintf
    (fun ff -> pp_print_flush ff () ; raise @@ Unif (Buffer.contents buf))
    ff fmt

let compatible v t =
  match vtag v with
  | E -> true
  | U -> begin
      match t.term with
      | Var u when vtag u = U -> true
      | _ -> false
    end

let is_evar v = vtag v = E
let is_evar_term t =
  match t.term with
  | Var v -> is_evar v
  | _ -> false

let is_param v = vtag v = U
let is_param_term t =
  match t.term with
  | Var v -> is_param v
  | _ -> false

let rec vnorm ss t =
  match t.term with
  | Var v when VMap.mem v ss ->
      vnorm ss (VMap.find v ss)
  | _ -> t

(* let join ?depth ss v t = *)
(*   Format.( *)
(*     fprintf std_formatter "Set: %s <-- %a@." v.rep (format_term ()) t *)
(*   ) ; *)
(*   Term.join ?depth ss v t *)

let rec unite ?depth ?(frz=VSet.empty) ss t1 t2 =
  let t1 = vnorm ss t1 in
  let t2 = vnorm ss t2 in
  (* Format.( *)
  (*   fprintf std_formatter "Unite: %a == %a [%s]@." *)
  (*     (format_term ()) t1 *)
  (*     (format_term ()) t2 *)
  (*     (String.concat "," @@ List.map (fun v -> v.rep) (IdtSet.elements frz)) *)
  (* ) ; *)
  if t1 = t2 then (ss, t1) else
  match t1.term, t2.term with
  | Var v1, Var v2 when is_param v1 && is_evar v2 ->
      unite ?depth ~frz ss t2 t1
  | Var v1, _ ->
      if not @@ compatible v1 t2 then unif_fail "variable incompatibility" ;
      if VSet.mem v1 frz then unif_fail "frozen variable" ;
      let t = replace ?depth ~repl:ss t2 in
      if VSet.mem v1 t.vars then unif_fail "occur check" ;
      (join ?depth ss v1 t, t)
  | _, Var v2 ->
      unite ?depth ~frz ss t2 t1
  | App (f1 as f, ts1), App (f2, ts2) when f1 == f2 ->
      let (ss, ts) = unite_lists ?depth ~frz ss ts1 ts2 in
      (ss, app f ts)
  | App (f1, _), App (f2, _) ->
      unif_fail "function-function: %s != %s" f1.rep f2.rep
  | Idx m, Idx n ->
      if m == n then
        Debug.bugf "Unify.unite: identical indexes (%d) in main loop" m ;
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
      (ss, replace ~repl:ss t :: ts)
  | _ -> unif_fail "argument lists not the same length"

module Test () = struct
  let eq x y = app (intern "eq") [x ; y]
  let f x = app (intern "f") [x]
  let g x = app (intern "g") [x]

  let v1 = Term.vargen#next E
  let v2 = Term.vargen#next E

  let t1 = eq v1 v1
  let t2 = eq v2 (f v2)

  let doit t1 t2 =
    Format.(
      fprintf std_formatter "Problem: %a == %a@."
        (format_term ()) t1
        (format_term ()) t2
    ) ;
    unite VMap.empty t1 t2

end
