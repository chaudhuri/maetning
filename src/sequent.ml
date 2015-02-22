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
    right : latm option ;
    vars : IdtSet.t ;
    (** invariant: fvs(sq.left) \cup fvs(sq.right) \subseteq sq.vars *)
    inits : ISet.t
  }
  val mk_sequent : left:ctx -> right:latm option -> inits:ISet.t -> sequent
end = struct
  type sequent = {sqid : int ; left : ctx ; right : latm option ;
                  vars : IdtSet.t ; inits : ISet.t}

  let next_sqid =
    let __last = ref 0 in
    fun () -> incr __last ; !__last

  let mk_sequent ~left ~right ~inits =
    let sqid = next_sqid () in
    let terms = match right with
      | None -> left
      | Some right -> Ft.snoc left right
    in
    let vars = Ft.fold_left begin
        fun vars (_, ts) ->
          List.fold_left begin
            fun vars t -> IdtSet.union vars t.Term.vars
          end vars ts
      end IdtSet.empty terms in
    { sqid ; left ; right ; vars ; inits}
end

include Sq

let freshen_latm ~repl (lab, args) =
  let (repl, args) = List.fold_left begin
      fun (repl, args) arg ->
        let (repl, arg) = Term.freshen ~repl arg in
        (repl, arg :: args)
    end (repl, []) args in
  let args = List.rev args in
  (repl, (lab, args))

let freshen_latm_option ~repl lopt =
  match lopt with
  | None -> (repl, None)
  | Some l ->
      let (repl, l) = freshen_latm ~repl l in
      (repl, Some l)

let freshen ?(repl=IdtMap.empty) s0 =
  let (repl, right) = freshen_latm_option ~repl s0.right in
  let (repl, left) = Ft.fold_left begin
      fun (repl, left) elem ->
        let (repl, elem) = freshen_latm ~repl elem in
        (repl, Ft.snoc left elem)
    end (repl, Ft.empty) s0.left in
  mk_sequent ~left ~right ~inits:s0.inits

let subsume_one ~repl (p, pargs) cx =
  let rec spin repls cx =
    match Ft.front cx with
    | Some (cx, (q, qargs)) -> begin
        let repls =
          try fst (Unify.unite_lists ~sym:false repl pargs qargs) :: repls
          with Unify.Unif _ -> repls
        in
        spin repls cx
      end
    | None -> repls
  in
  spin [] cx

let subsume_all_exn ~repl scx tcx =
  let rec gen repl scx =
    match Ft.front scx with
    | Some (scx, l) ->
        let repls = subsume_one ~repl l tcx in
        test repls scx
    | None -> repl
  and test repls scx =
    match repls with
    | [] -> Unify.unif_fail "all"
    | repl :: repls -> begin
        try gen repl scx
        with Unify.Unif _ -> test repls scx
      end
  in
  gen repl scx

let subsume_full_exn ss0 tt0 =
  let repl = IdtMap.empty in
  let repl =
    match ss0.right, tt0.right with
    | None, rt -> repl
    | Some (p, pargs), Some (q, qargs) when p == q ->
        let (repl, _) = Unify.unite_lists ~sym:false repl pargs qargs in
        repl
    | _ -> Unify.unif_fail "right"
  in
  subsume_all_exn ~repl ss0.left tt0.left

let subsume_test_right sr0 tr0 =
  match sr0, tr0 with
  | None, _ -> true
  | Some (p, pargs), Some (q, args) -> p == q
  | _ -> false

let subsume_test_left sl0 tl0 =
  let rec test p l =
    match Ft.front l with
    | Some (l, (q, _)) ->
        p == q || test p l
    | None -> false
  and gen l =
    match Ft.front l with
    | None -> true
    | Some (l, (p, _)) ->
        test p tl0 && gen l
  in
  gen sl0

let subsume ss0 tt0 =
  subsume_test_right ss0.right tt0.right &&
  subsume_test_left ss0.left tt0.left &&
  begin
    try ignore (subsume_full_exn ss0 tt0) ; true
    with Unify.Unif _ -> false
  end
