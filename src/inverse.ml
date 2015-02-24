(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* prover internals *)

open Batteries

open Term
open Form
open Rule
open Sequent

module type Data = sig
  val reset : unit -> unit
  val register : Sequent.t -> unit
  val select : unit -> Sequent.t option
  val iter_active : (Sequent.t -> 'a) -> unit
end

module Trivial : Data = struct
  let sos : Sequent.t Queue.t = Queue.create ()
  let active : Sequent.t list ref = ref []
  let db : Sequent.t list ref = ref []

  let reset () =
    Queue.clear sos ;
    active := [] ;
    db := []

  let subsumed sq =
    List.exists (fun oldsq -> Sequent.subsume oldsq sq) !db

  let index sq =
    Format.printf "[%d] %a@." sq.sqid (Sequent.format_sequent ()) sq ;
    db := sq :: !db ;
    Queue.add sq sos

  let register sq =
    if not @@ subsumed sq then index sq

  let select () =
    try
      let sel = Queue.take sos in
      active := sel :: !active ;
      Some sel
    with Queue.Empty -> None

  let iter_active doit =
    List.iter (fun sq -> ignore (doit sq)) !active
end

let rec spin_until_none get op =
  match get () with
  | None -> ()
  | Some item -> op item ; spin_until_none get op

let rec spin_until_quiescence measure op =
  let before = measure () in
  op () ;
  let after = measure () in
  if before != after then spin_until_quiescence measure op

let noop () = ()

module Inv (D : Data) = struct
  exception Escape of Sequent.t

  let inverse_method ?(left=[]) ?(pseudo=[]) ?(per_loop=noop) right =
    try
      D.reset () ;
      let rules = ref [] in
      let (goal_lf, gen) = Rule_gen.generate0 left pseudo right in
      let goal_seq = mk_sequent ~right:(goal_lf.label, goal_lf.args) () in
      let add_seq sq =
        if Sequent.subsume sq goal_seq then raise (Escape sq) ;
        D.register sq
      in
      let add_rule rr =
        match rr.prems with
        | [] ->  add_seq rr.concl
        | _ ->
            (* Rule.Test.print rr ; *)
            rules := rr :: !rules
      in
      gen ~sc_inits:add_seq ~sc_rules:add_rule ;
      spin_until_none D.select begin fun sel ->
        List.iter begin fun rr ->
          Rule.specialize_default rr (Sequent.freshen sel ())
            ~sc_rule:add_rule
            ~sc_fact:add_seq
        end !rules ;
        spin_until_quiescence (fun () -> List.length !rules) begin fun () ->
          List.iter begin fun rr ->
            D.iter_active begin fun act ->
              Rule.specialize_default rr (Sequent.freshen act ())
                ~sc_rule:add_rule
                ~sc_fact:add_seq
            end
          end !rules
        end ;
        per_loop () ;
      end ;
      None
    with Escape sq -> Some sq
end

include Inv(Trivial)

module Test = struct
  open Idt
  open Rule_gen.Test

  let even x = Form.atom NEG (intern "even") [x]
  let even_theory = [ even z ;
                      forall (intern "x") (implies [even (idx 0)] (even (s (s (idx 0))))) ]
  let even_prune n =
    let rec prune_t t = function
      | 0 -> forall (intern "x") (even t)
      | n -> prune_t (s t) (n - 1)
    in [ prune_t (idx 0) n ]
  let even_right = even (s (s (s z))) |> shift

  let even_test n =
    match inverse_method ~left:even_theory ~pseudo:(even_prune n) even_right with
    | None ->
        Format.printf "Not provable@."
    | Some pf -> begin
        match
          Ft.to_list pf.left |>
          List.Exceptionless.find (fun (p, _) -> Form.is_pseudo p)
        with
        | None -> Format.printf "Proved!@."
        | Some (p, _) -> Format.printf "UNSOUND: Used pseudo %s.@." p.rep
      end

  let lf = app (intern "lf") []
  let nd tl tr = app (intern "nd") [tl ; tr]
  let bal t x = atom NEG (intern "bal") [t ; x]
  let bal_th = [ bal lf z ;
                 forall (intern "x")
                   (forall (intern "t")
                      (let t = idx 0 in
                       let x = idx 1 in
                       implies [bal t x] (bal (nd t t) (s x)))) ]
  let bal_prune n =
    let rec spin t = function
      | 0 -> wrap (forall (intern "x") (bal t (idx 0))) (n + 1)
      | k -> spin (nd t (idx (n - k + 2))) (k - 1)
    and wrap t = function
      | 0 -> t
      | k -> wrap (forall (intern ("tt" ^ string_of_int k)) t) (k - 1)
    in
    spin (idx 1) n
  let bal_right = exists (intern "x") (bal (nd lf (nd lf lf)) (idx 0))

  let baltest n =
    match inverse_method ~left:bal_th ~pseudo:[ bal_prune n ] bal_right with
    | None ->
        Format.printf "Not provable@."
    | Some pf -> begin
        match
          Ft.to_list pf.left |>
          List.Exceptionless.find (fun (p, _) -> Form.is_pseudo p)
        with
        | None -> Format.printf "Proved!@."
        | Some (p, _) -> Format.printf "UNSOUND: Used pseudo %s.@." p.rep
      end
end
