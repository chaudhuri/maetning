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
    Sequent.Test.print sq ;
    db := sq :: !db ;
    Queue.add sq sos

  let register sq =
    if not (subsumed sq) then index sq
    (* else Format.printf "Subsumed: %a@." (Sequent.format_sequent ()) sq *)

  let select () =
    try
      let sel = Queue.take sos in
      active := sel :: !active ;
      Some (Sequent.freshen sel ())
    with Queue.Empty -> None

  let iter_active doit =
    List.iter (fun sq -> ignore (doit (Sequent.freshen sq ()))) !active
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

let rec percolate ~sc_fact ~sc_rule rules iter =
  let new_rules = percolate_once ~sc_fact rules iter in
  List.iter sc_rule new_rules ;
  if new_rules <> [] then percolate ~sc_fact ~sc_rule new_rules iter

and percolate_once ~sc_fact rules iter =
  let new_rules = ref [] in
  let add_rule rr =
    match rr.prems with
    | [] -> sc_fact rr.concl
    | _ ->
        if not @@ List.exists (fun oldrr -> Rule.rule_subsumes oldrr rr) !new_rules then
          new_rules := rr :: !new_rules
  in
  List.iter begin fun rr ->
    iter begin fun sq ->
      Rule.specialize_default rr sq
        ~sc_fact
        ~sc_rule:add_rule
    end
  end rules ;
  !new_rules


let noop () = ()

module Inv (D : Data) = struct
  exception Escape of (Format.formatter -> unit) * Sequent.t

  let inverse_method ?(left=[]) ?(pseudo=[]) ?(per_loop=noop) right =
    try
      D.reset () ;
      let rules = ref [] in
      let (goal_lf, gen_expl, gen) = Rule_gen.generate0 left pseudo right in
      let goal_seq = mk_sequent ~right:(goal_lf.label, goal_lf.args) () in
      (* Format.printf "Goal sequent: %a@." (Sequent.format_sequent ()) goal_seq ; *)
      let add_seq sq =
        if Sequent.subsume sq goal_seq then begin
          Sequent.Test.print sq ;
          (* Format.printf "[%d] %a@." sq.sqid (Sequent.format_sequent ()) sq ; *)
          raise (Escape (gen_expl, sq))
        end ;
        D.register sq
      in
      let add_rule rr =
        match rr.prems with
        | [] ->  add_seq rr.concl
        | _ ->
            if not @@ List.exists (fun oldrr -> Rule.rule_subsumes oldrr rr) !rules then begin
              Rule.Test.print rr ;
              rules := rr :: !rules
            end
      in
      gen ~sc:add_rule ;
      spin_until_none D.select begin fun sel ->
        (* Format.printf "Selected: %a@." (Sequent.format_sequent ()) sel ; *)
        (* let new_rules = ref [] in *)
        (* let add_new_rule rr = *)
        (*   match rr.prems with *)
        (*   | [] ->  add_seq rr.concl *)
        (*   | _ -> *)
        (*       Rule.Test.print rr ; *)
        (*       new_rules := rr :: !new_rules *)
        (* in *)
        percolate !rules (fun doit -> doit sel)
          ~sc_rule:add_rule ~sc_fact:add_seq ;
        (* List.iter begin fun rr -> *)
        (*   Rule.specialize_default rr sel *)
        (*     ~sc_rule:add_new_rule *)
        (*     ~sc_fact:add_seq ; *)
        (* end !rules ; *)
        percolate !rules D.iter_active
          ~sc_rule:add_rule ~sc_fact:add_seq ;
        (* spin_until_quiescence (fun () -> List.length !new_rules) begin fun () -> *)
        (*   List.iter begin fun rr -> *)
        (*     D.iter_active begin fun act -> *)
        (*       Rule.specialize_default rr act *)
        (*         ~sc_rule:add_new_rule *)
        (*         ~sc_fact:add_seq *)
        (*     end ; *)
        (*   end !new_rules ; *)
        (* end ; *)
        (* List.iter add_rule !new_rules ; *)
        per_loop () ;
      end ;
      None
    with Escape (expl, sq) -> Some (expl, sq)
end

include Inv(Trivial)

module Test = struct
  open Idt
  open Rule_gen.Test

  let sleep n () =
    Format.printf "One loop done@." ;
    Unix.sleep n

  let inverse_test ~theory ~pseudo ~goal ?(per_loop=noop) n =
    match inverse_method ~left:theory ~pseudo:(pseudo n) ~per_loop goal with
    | None ->
        Format.printf "Not provable@."
    | Some (_, pf) -> begin
        match
          Ft.to_list pf.left |>
          List.Exceptionless.find (fun (p, _) -> Form.is_pseudo p)
        with
        | None -> Format.printf "Proved!@."
        | Some (p, _) -> Format.printf "UNSOUND: Used pseudo %s.@." p.rep
      end

  let rec s_n n x = match n with 0 -> x | n -> s (s_n (n - 1) x)

  let even x = Form.atom NEG (intern "even") [x]
  let even_theory = [ even z ;
                      forall_ "x" (fun x -> implies [even x] (even (s (s x)))) ]
  let even_prune n = [ forall_ "x" (fun x -> even (s_n n x)) ]
  let even_prune n = [ ]
  let even_right = even (s_n 2 z) |> shift
  let even_test n = inverse_test ~theory:even_theory ~pseudo:even_prune ~goal:even_right n

  let odd x = Form.atom NEG (intern "odd") [x]
  let odd_theory = [ odd (s z) ;
                     forall_ "x" (fun x -> implies [odd (s_n 2 x)] (odd x)) ]
  let odd_prune_unguarded n = [
      (forall_ "x" (fun x -> odd (s_n n x)))
  ]
  let odd_prune_guarded n = [
    implies [exists_ "x" (fun x -> odd (s_n n x))]
      (forall_ "x" (fun x -> odd (s_n n x)))
  ]
  let odd_goal = odd (s (s z)) |> shift
  let odd_test_guarded n = inverse_test n
      ~theory:odd_theory
      ~pseudo:odd_prune_guarded
      ~goal:odd_goal
  let odd_test_unguarded n = inverse_test n
      ~theory:odd_theory
      ~pseudo:odd_prune_unguarded
      ~goal:odd_goal

  let lf = app (intern "lf") []
  let nd tl tr = app (intern "nd") [tl ; tr]
  let bal t x = atom NEG (intern "bal") [t ; x]
  let bal_th = [ bal lf z ;
                 forall_ "x"
                   (fun x -> forall_ "t"
                       (fun t -> implies [bal t x] (bal (nd t t) (s x)))) ]
  let bal_prune n =
    let rec spin t = function
      | 0 -> wrap (forall (intern "x") (bal t (idx 0))) (n + 1)
      | k -> spin (nd t (idx (n - k + 2))) (k - 1)
    and wrap t = function
      | 0 -> t
      | k -> wrap (forall (intern ("tt" ^ string_of_int k)) t) (k - 1)
    in
    [ spin (idx 1) n ]
  let bal_right = exists (intern "x") (bal (nd lf (nd lf lf)) (idx 0))
  let bal_test n = inverse_test ~theory:bal_th ~pseudo:bal_prune ~goal:bal_right n

end
