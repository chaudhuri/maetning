(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014,2015  Inria
 *     (Institut National de Recherche en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries

open Idt

type vkind = U | E
type var = int

module VOrd = struct
  type t = var
  let compare u v = u - v
end
module VSet = Set.Make(VOrd)
module VMap = struct
  include Map.Make(VOrd)
  let digest bs : 'a t =
    List.fold_left (fun repl (x, t) -> add x t repl) empty bs
  let insert m x t = add x t m
end

type term = {
  term : term_ ;
  vars : VSet.t ;
  (** invariant: fvs(t) \subseteq t.vars   *)
  imax : int ;
  (** invariant: max(-1::fbs(t)) <= t.imax *)
}
and term_ =
  | Var of var
  | Idx of int
  | App of idt * term list

let idx n = {
  term = Idx n ;
  vars = VSet.empty ;
  imax = max n @@ -1 ;
}

type repl = term VMap.t

let var u = {term = Var u ; vars = VSet.singleton u ; imax = -1}
let vtag u = if u mod 2 = 0 then U else E
let uvar u = var (- 2 * u)
let evar u = var (- 2 * u - 1)

let unvar t =
  match t.term with
  | Var v -> v
  | _ -> failwith "unvar"

let app f ts = {
  term = App (f, ts) ;
  imax =
    List.fold_left (fun mx t -> max mx t.imax) (-1) ts ;
  vars =
    List.fold_left
      (fun vs t -> VSet.union vs t.vars) VSet.empty ts ;
}

let vargen = new Namegen.namegen1
  (fun u k -> if k = U then uvar u else evar u)

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

let rec freeze_term ?(frz=VSet.empty) t =
  match t.term with
  | Var v -> VSet.add v frz
  | Idx _ -> frz
  | App (f, ts) -> freeze_terms ~frz ts

and freeze_terms ?(frz=VSet.empty) ts =
  match ts with
  | [] -> frz
  | t :: ts ->
      let frz = freeze_term ~frz t in
      freeze_terms ~frz ts

let rec replace ?(depth=0) ~repl t0 =
  if VSet.for_all (fun v -> not @@ VMap.mem v repl) t0.vars
  then t0
  else match t0.term with
    | Var u -> begin
        match VMap.find u repl with
        | t1 -> app_term (Shift depth) t1
        | exception Not_found -> t0
      end
    | Idx _ -> t0
    | App (f, ts) -> app f (List.map (replace ~depth ~repl) ts)

let replace_eigen ~repl v =
  match VMap.find v repl with
  | t -> unvar t
  | exception Not_found -> v

let replace_eigen_list ~repl evs =
  List.fold_left begin
    fun evs v ->
      replace_eigen ~repl v :: evs
  end [] evs

let replace_eigen_set ~repl evset =
  VSet.fold begin
    fun v evset ->
      VSet.add (replace_eigen ~repl v) evset
  end evset VSet.empty

let join ?depth ss v t =
  let vtss = VMap.digest [v, t] in
  let ss = VMap.map (replace ?depth ~repl:vtss) ss in
  VMap.add v t ss

let freshen_var u = vargen#next (vtag u)

let rec freshen ?depth ~repl t0 =
  let repl = VSet.fold begin fun v repl ->
      if VMap.mem v repl then repl else
      join repl v @@ freshen_var v
    end t0.vars repl in
  (repl, replace ?depth ~repl t0)

let canonize_var u n =
  if u > 0 then uvar n else evar n

let canonize ~repl t0 =
  VSet.fold begin fun v repl ->
    if VMap.mem v repl then repl else
      VMap.insert repl v (canonize_var v @@ 1 + VMap.cardinal repl)
  end t0.vars repl

let canonize_list ~repl ts =
  List.fold_left (fun repl t -> canonize ~repl t) repl ts

let compact_print = ref true

let format_var fmt v =
  let cookie = match vtag v with U ->  "'" | E ->  "?" in
  Format.(
    pp_print_string fmt cookie ;
    pp_print_int fmt (abs v)
  )

let var_to_string v =
  let cookie = match vtag v with U ->  "'" | E ->  "?" in
  cookie ^ string_of_int v

let rec format_term ?(cx=[]) ?max_depth () fmt t =
  let open Format in
  let ellipse = match max_depth with
    | None -> false
    | Some d -> d <= 0 in
  if ellipse then pp_print_string fmt "_" else
  match t.term with
  | Var v -> format_var fmt v
  | Idx n when n < List.length cx ->
      pp_print_string fmt (List.nth cx n).rep
  | Idx n ->
      pp_print_char fmt '`' ; pp_print_int fmt n
  | App (f, []) ->
      pp_print_string fmt f.rep
  | App (f, _) when max_depth = Some 1 ->
      pp_print_string fmt f.rep ;
      pp_print_string fmt "(...)"
  | App (f, [t]) -> begin
      let (n, t) = collect f t in
      let max_depth = match max_depth with
        | None -> None
        | Some d -> Some (d - 1) in
      pp_open_hvbox fmt 2 ; begin
        pp_print_string fmt f.rep ;
        if n > 1 then begin
          let s = string_of_int n in
          pp_print_as fmt (String.length s) (make_superscript s) ;
        end ;
        pp_print_string fmt "(" ;
        format_term ~cx ?max_depth () fmt t ;
        pp_print_string fmt ")" ;
      end ; pp_close_box fmt () ;
    end
  | App (f, t0 :: ts) -> begin
      let max_depth = match max_depth with
        | None -> None
        | Some d -> Some (d - 1) in
      pp_open_hvbox fmt 2 ; begin
        pp_print_string fmt f.rep ;
        (* pp_print_cut fmt () ; *)
        pp_print_string fmt "(" ;
        format_term ~cx ?max_depth () fmt t0 ;
        List.iter begin fun t ->
          pp_print_string fmt "," ;
          if !compact_print then pp_print_cut fmt ()
          else pp_print_space fmt () ;
          format_term ~cx ?max_depth () fmt t ;
        end ts ;
        pp_print_string fmt ")" ;
      end ; pp_close_box fmt () ;
    end

and collect f ?(n = 1) t =
  match t.term with
  | App (g, [t]) when f == g -> collect f ~n:(n + 1) t
  | _ -> (n, t)

and make_superscript s =
  String.replace_chars begin fun c ->
    match c with
    | '0' -> "⁰" | '1' -> "¹" | '2' -> "²" | '3' -> "³" | '4' -> "⁴"
    | '5' -> "⁵" | '6' -> "⁶" | '7' -> "⁷" | '8' -> "⁸" | '9' -> "⁹"
    | _ -> String.of_char c
  end s

let term_to_string ?(cx=[]) ?max_depth t =
  let buf = Buffer.create 19 in
  let fmt = Format.formatter_of_buffer buf in
  format_term ~cx ?max_depth () fmt t ;
  Format.pp_print_flush fmt () ;
  Buffer.contents buf

let format_repl fmt repl =
  let open Format in
  pp_open_hvbox fmt 1 ; begin
    pp_print_string fmt "{" ;
    VMap.iter begin fun v t ->
      format_var fmt v ;
      pp_print_string fmt ":= " ;
      format_term () fmt t ;
      pp_print_string fmt ";" ;
      pp_print_space fmt () ;
    end repl ;
    pp_print_string fmt "}" ;
  end ; pp_close_box fmt ()
