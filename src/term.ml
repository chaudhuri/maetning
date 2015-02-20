(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014  INRIA (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Idt

type term = {
  term : term_ ;
  vars : IdtSet.t ;
  (** invariant: fvs(t) \subseteq t.vars   *)
  imax : int ;
  (** invariant: max(-1::fbs(t)) <= t.imax *)
}
and term_ =
  | Var of Idt.t
  | Idx of int
  | App of idt * term list

let idx n = {
  term = Idx n ;
  vars = IdtSet.empty ;
  imax = max n @@ -1 ;
}

let evar_cookie = "?"
let param_cookie = "\'"

let var v =
  assert (v.rep.[0] == evar_cookie.[0] || v.rep.[0] == param_cookie.[0]) ;
  { term = Var v ;
    vars = IdtSet.singleton v ;
    imax = -1 }

let app f ts = {
  term = App (f, ts) ;
  imax =
    List.fold_left (fun mx t -> max mx t.imax) (-1) ts ;
  vars =
    List.fold_left
      (fun vs t -> IdtSet.union vs t.vars) IdtSet.empty ts ;
}

let fresh_var =
  let last = ref 0 in
  fun (flav : [`evar | `param]) ->
    incr last ;
    let v = match flav with
      | `evar -> intern (evar_cookie ^ string_of_int !last)
      | `param -> intern (param_cookie ^ string_of_int !last)
    in
    { term = Var v ; vars = IdtSet.singleton v ; imax = -1 }

type sub =
  | Shift of int
  | Cons  of sub * term
  | Bump  of sub * int          (* ss^n := (^n ss).(n - 1)...0 *)
  | Seq   of sub * sub

let rec app_idx sub n =
  match sub with
  | Shift m -> idx (n + m)
  | Cons (_, t) when n = 0 -> t
  | Cons (sub, _) -> app_idx sub (n - 1)
  | Bump (_, m) when n < m -> idx n
  | Bump (sub, m) -> app_idx sub (n - m)
  | Seq (sub1, sub2) ->
      app_idx sub2 n |>
      app_term sub1

and app_term sub t0 =
  if t0.imax < 0 then t0
  else match sub with
    | Bump (sub, n) when t0.imax < n -> t0
    | _ -> begin match t0.term with
        | Var _ -> t0
        | Idx n -> app_idx sub n
        | App (f, ts) -> app f (List.map (app_term sub) ts)
      end

let bump sub n =
  match sub with
  (* id^n = id *)
  | Shift 0 -> sub
  (* (ss^m)^n = ((^m ss).(m - 1)...0)^n                     *)
  (*          = (^n ((^m ss).(m - 1)...0)).(n - 1)...0      *)
  (*          = ((^(n + m) ss).(n + m - 1)...n).(n - 1)...0 *)
  (*          = (^(n + m) ss).(n + m - 1)...0               *)
  (*          = ss^(n + m)                                  *)
  | Bump (sub, m) -> Bump (sub, n + m)
  (* otherwise *)
  | _ -> if n = 0 then sub else Bump (sub, n)

let rec seq ss1 ss2 =
  match ss1, ss2 with
  | Shift 0, _ -> ss2
  | _, Shift 0 -> ss1
  | _, Seq (ss21, ss22) -> Seq (seq ss1 ss21, ss22)
  | _ -> Seq (ss1, ss2)

let rec replace ?(depth=0) ~repl t0 =
  if IdtSet.for_all (fun v -> not @@ IdtMap.mem v repl) t0.vars
  then t0
  else match t0.term with
    | Var u -> begin
        match IdtMap.find_opt u repl with
        | Some t1 -> app_term (Shift depth) t1
        | None -> t0
      end
    | Idx _ -> t0
    | App (f, ts) -> app f (List.map (replace ~depth ~repl) ts)

let join ?depth ss v t =
  let vtss = IdtMap.digest [v, t] in
  let ss = IdtMap.map (replace ?depth ~repl:vtss) ss in
  IdtMap.insert ss v t

let freshen_var =
  let last = ref 0 in
  fun v ->
    let prefix =
      try String.sub v.rep 0 (String.rindex v.rep '#')
      with Not_found -> v.rep
    in
    incr last ;
    var @@ intern @@ prefix ^ "#" ^
                     string_of_int !last

let rec freshen ?depth ~repl t0 =
  let repl = IdtSet.fold begin fun v repl ->
      if IdtMap.mem v repl then repl else
      join repl v @@ freshen_var v
    end t0.vars repl in
  (repl, replace ?depth ~repl t0)

let rec format_term ?(cx=[]) ?max_depth () fmt t =
  let open Format in
  let ellipse = match max_depth with
    | None -> false
    | Some d -> d <= 0 in
  if ellipse then pp_print_string fmt "_" else
  match t.term with
  | Var v ->
      pp_print_string fmt v.rep
  | Idx n ->
      assert (n < List.length cx) ;
      pp_print_string fmt (List.nth cx n).rep
  | App (f, []) ->
      pp_print_string fmt f.rep
  | App (f, _) when max_depth = Some 1 ->
      pp_print_string fmt f.rep ;
      pp_print_string fmt "(...)"
  | App (f, t0 :: ts) -> begin
      let max_depth = match max_depth with
        | None -> None
        | Some d -> Some (d - 1) in
      pp_open_hvbox fmt 2 ; begin
        pp_print_string fmt f.rep ;
        pp_print_string fmt "(" ;
        pp_print_cut fmt () ;
        format_term ~cx ?max_depth () fmt t0 ;
        List.iter begin fun t ->
          pp_print_string fmt "," ;
          pp_print_space fmt () ;
          format_term ~cx ?max_depth () fmt t ;
        end ts ;
        pp_print_string fmt ")" ;
      end ; pp_close_box fmt () ;
    end

let term_to_string ?(cx=[]) ?max_depth t =
  let buf = Buffer.create 19 in
  let fmt = Format.formatter_of_buffer buf in
  format_term ~cx ?max_depth () fmt t ;
  Format.pp_print_flush fmt () ;
  Buffer.contents buf
