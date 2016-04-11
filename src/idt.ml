(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014,2015  Inria
 *     (Institut National de Recherche en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries

type idt = { rep : string ; idx : int }

module IdtHash = struct
  type t = idt
  let equal (id1 : idt) id2 = id1.rep = id2.rep
  let hash (id : idt) = Hashtbl.hash id.rep
end
module IdTab = Weak.Make (IdtHash)
module IdHash = Hashtbl.Make (IdtHash)

let intern : string -> idt =
  let idtab = IdTab.create 109 in
  let last_idx = ref 0 in
  fun id ->
    incr last_idx ;
    let cand = { rep = id ; idx = !last_idx } in
    let idt = IdTab.merge idtab cand in
    if idt.idx != cand.idx then decr last_idx ;
    idt

module IdtOrdered = struct
  type t = idt
  let compare (id1 : idt) id2 =
    if id1.idx < id2.idx then -1
    else if id1.idx > id2.idx then 1
    else 0
end

module IdtSet = struct
  include Set.Make (IdtOrdered)
  let insert set elt = add elt set
  let pp ff set =
    let open Format in
    pp_open_box ff 0 ; begin
      let elts = elements set in
      match elts with
      | [] -> ()
      | [x] -> fprintf ff "%s" x.rep
      | x :: xs ->
          fprintf ff "%s" x.rep ;
          List.iter begin fun x ->
            fprintf ff "@, %s" x.rep
          end xs
    end ; pp_close_box ff ()
end

module IdtMap = struct
  include Map.Make (IdtOrdered)
  let insert m k v = add k v m
  let digest kvs = List.fold_left (fun m (k, v) -> add k v m) empty kvs
  let find_opt k m =
    try Some (find k m) with Not_found -> None
  let pp vfn ff m =
    let open Format in
    pp_open_box ff 0 ; begin
      let binds = bindings m in
      match binds with
      | [] -> ()
      | [x, v] -> fprintf ff "%s:%a" x.rep vfn v
      | (x, v) :: binds ->
          fprintf ff "%s:%a" x.rep vfn v ;
          List.iter begin fun (x, v) ->
            fprintf ff "@, %s:%a" x.rep vfn v
          end binds
    end ; pp_close_box ff ()
end

type t = idt
