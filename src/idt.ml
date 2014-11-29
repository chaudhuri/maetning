(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014  INRIA (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

type idt = { rep : string ; idx : int }

module IdtHash = struct
  type t = idt
  let equal (id1 : idt) id2 = id1.rep = id2.rep
  let hash (id : idt) = Hashtbl.hash id.rep
end
module IdTab = Weak.Make (IdtHash)

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
    Pervasives.compare id1.idx id2.idx
end

module IdtSet = struct
  include Set.Make (IdtOrdered)
  let insert set elt = add elt set
end

module IdtMap = struct
  include Map.Make (IdtOrdered)
  let insert m (k, v) = add k v m
  let digest kvs = List.fold_left insert empty kvs
  let find_opt k m =
    try Some (find k m) with Not_found -> None
end

type t = idt
