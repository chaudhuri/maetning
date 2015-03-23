(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries

open Idt

type t = int IdtMap.t

let varsplit s =
  let point = ref (String.length s) in
  let rec all_zeros from =
    from < 0 || begin
      match s.[from] with
      | '1' .. '9' -> false
      | '0' -> all_zeros (from - 1)
      | _ -> true
    end in
  let rec find_point () =
    if !point != 0 then begin
      decr point ;
      match s.[!point] with
      | '1'..'9' -> find_point ()
      | '0' ->
          if all_zeros !point then incr point
          else find_point ()
      | _ ->
          incr point
    end
  in
  find_point () ;
  let left = String.sub s 0 !point in
  let right =
    match String.sub s !point (String.length s - !point) with
    | "" -> 0
    | n -> int_of_string n
  in
  left, right

let fresh_wrt nst x0 =
  let (x, salt) = varsplit x0.rep in
  let x = Idt.intern x in
  match IdtMap.find x nst with
  | m ->
      let n = max salt (m + 1) in
      let nst = IdtMap.add x n nst in
      (nst, Idt.intern (x.rep ^ string_of_int n))
  | exception Not_found ->
      (IdtMap.add x 0 nst, x0)
