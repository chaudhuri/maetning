(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries
module Ft = FingerTree

open Idt
open Term

type latm = idt * term list
type ctx = (latm, int) Ft.fg

let ctx_splits ~sc ctx =
  let rec spin left right =
  match Ft.front right with
  | Some (right, x) ->
      sc x (Ft.append left right) ;
      spin (Ft.snoc left x) right
  | None -> ()
  in
  spin Ft.empty ctx

let to_list : ctx -> (idt * term list) list =
  Ft.to_list

module Sq : sig
  type sequent = private {
    sqid : int ;
    left : ctx ;
    right : latm ;
    vars : IdtSet.t ;
    (** invariant: fvs(sq.left) \cup fvs(sq.right) \subseteq sq.vars *)
  }
  val mk_sequent : left:ctx -> right:latm -> sequent
end = struct
  type sequent = {sqid : int ; left : ctx ; right : latm ; vars : IdtSet.t}

  let next_sqid =
    let __last = ref 0 in
    fun () -> incr __last ; !__last

  let mk_sequent ~left ~right =
    let sqid = next_sqid () in
    let vars = Ft.fold_left begin
        fun vars (_, ts) ->
          List.fold_left begin
            fun vars t -> IdtSet.union vars t.Term.vars
          end vars ts
      end IdtSet.empty (Ft.snoc left right) in
    { sqid ; left ; right ; vars }
end

include Sq
