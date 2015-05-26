(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries

open Idt

open Term
open Form

module IM = Map.Make (Int)

type tr = Tr of node * tr list
and node = {
  fp : int list list ;
  load : (idt * spine) IM.t ;
  repl : term VMap.t ;
  last : int ;
}
and spine = term list

let init p args =
  let root = {
    fp = [[1]] ;
    load = IM.add 1 (p, args) IM.empty ;
    repl = VMap.empty ;
    last = 1
  } in
  Tr (root, [])

let rec expand p args (Tr (root, kids)) =
  let last = root.last + 1 in
  let fp = [ last ] :: root.fp in
  let load = IM.add last (p, args) root.load in
  let kids = List.map (expand p args) kids in
  let new_kids = ref [] in
  let compatible ch =
    match IM.find (List.hd ch) load with
    | (q, qargs) ->
        if p != q then Unify.unif_fail "relations differ" ;
        Unify.unite_lists root.repl args qargs
    | exception Not_found ->
        assert false
  in
  let rec distribute left right =
    match right with
    | [] -> ()
    | ch :: right ->
        begin match compatible ch with
        | (repl, args) ->
            let load = IM.add last (p, args) root.load in
            let root = {
              fp = List.rev_append left ((last :: ch) :: right) ;
              load ; last ; repl
            } in
            new_kids := Tr (root, []) :: !new_kids ;
        | exception Unify.Unif _ -> ()
        end ;
        distribute (ch :: left) right
  in
  distribute [] root.fp ;
  let kids = List.rev_append !new_kids kids in
  let root = { fp ; load ; last ; repl = root.repl } in
  Tr (root, kids)

let bfs ~visit tr =
  let q = Queue.create () in
  Queue.add tr q ;
  while not @@ Queue.is_empty q do
    let Tr (root, kids) = Queue.pop q in
    visit root ;
    List.iter (fun k -> Queue.add k q) kids
  done

let restore_root root =
  (root.repl,
   root.fp |>
   List.map (fun ch -> IM.find (List.hd ch) root.load) |>
   List.map (fun (p, args) -> (p, List.map (Term.replace ~repl:root.repl) args)))

let factor ~sc sq =
  let open Sequent in
  let latms = Ft.to_list sq.left in
  match latms with
  | [] -> sc sq
  | (p, args) :: latms ->
      let tr = List.fold_left begin fun tr (p, args) ->
          expand p args tr
        end (init p args) latms
      in
      let sqs : sequent list ref = ref [] in
      let visit root =
        let (repl, left) = restore_root root in
        let left = Ft.of_list left in
        let right = Option.map (replace_latm ~repl) sq.right in
        sqs := override sq ~left ~right :: !sqs
      in
      bfs ~visit tr ;
      List.iter sc !sqs
