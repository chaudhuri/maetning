(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014,2015  Inria
 *     (Institut National de Recherche en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** Interned (hash-consed) strings *)

open Batteries

type idt = private {
  rep : string ;
  idx : int ;
}

(** [intern s] returns a shared version of [s].

    Invariant: if [s1 = s2], then [intern s1 == intern s2]. *)
val intern : string -> idt

module IdtSet : sig
  include Set.S
  val insert : t -> elt -> t
end with type elt := idt

module IdtMap : sig
  include Map.S
  val insert : 'v t -> key -> 'v -> 'v t
  val digest : (key * 'v) list -> 'v t
  val find_opt : key -> 'v t -> 'v option
end with type key := idt

type t = idt
