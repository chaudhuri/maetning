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

let __debug = false

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
    Format.(
      fprintf std_formatter "[%d] %a %t@."
        sq.sqid
        (format_sequent ()) sq
        (* Skeleton.format_skeleton sq.skel *)
        (fun ff -> if __debug then fprintf ff "[%a]" Skeleton.format_skeleton sq.skel)
    ) ;
    db := sq :: !db ;
    Queue.add sq sos

  let register sq =
    if not (subsumed sq) then index sq
    (* else Format.printf "Subsumed: %a@." (Sequent.format_sequent ()) sq *)

  let select () =
    try
      let sel = Queue.take sos in
      active := sel :: !active ;
      if __debug then
        Format.printf "Selected: [%d] %a@." sel.sqid (Sequent.format_sequent ()) sel ;
      let sel = Sequent.freshen sel () in
      if __debug then
        Format.printf " `--> [%d] %a@." sel.sqid (Sequent.format_sequent ()) sel ;
      Some sel
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

let is_new_rule_wrt rules rr =
  not @@ List.exists (fun oldrr -> Rule.rule_subsumes oldrr rr) rules

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
        if is_new_rule_wrt !new_rules rr &&
           is_new_rule_wrt rules rr
        then new_rules := rr :: !new_rules
  in
  List.iter begin fun rr ->
    iter begin fun sq ->
      Format.(
        if __debug then
          printf "  >>> Trying [%d] @[%a@]@.  >>> with %a@."
            sq.sqid (format_sequent ()) sq
            (format_rule ()) rr
      ) ;
      Rule.specialize_default rr sq
        ~sc_fact:(fun sq ->
            if __debug then
              Format.printf "  >>> produced sequent: [%d] @[%a@]@." sq.sqid (format_sequent ()) sq ;
            sc_fact sq
          )
        ~sc_rule:(fun rr ->
            if __debug then
              Format.printf "  >>> produced rule @[%a@]@." (format_rule ()) rr ;
            add_rule rr
          )
    end
  end rules ;
  !new_rules

let get_polarity ~lforms p =
  match List.find (fun lf -> lf.label == p) lforms with
  | exception Not_found ->
      Idt.IdtMap.find p !polarity_map
  | lf -> polarity lf.skel

let __paranoia = [
  (* `reconstruct ; *)
  (* `check ; *)
]
let paranoid_check ~lforms sq =
  if List.mem `reconstruct __paranoia then begin
    (* Seqproof.hypgen#reset ; *)
    Config.pprintf "<p>Paranoia for [%d]</p>@." sq.sqid ;
    let next_local =
      let current = ref 0 in
      fun () -> incr current ; Idt.intern ("v" ^ string_of_int !current)
    in
    let ctx_ambient = List.filter_map begin
        fun lf -> match lf.place with
          | Left Global ->
              Some (lf.label, (lf.label, lf.Form.skel))
          | Left Pseudo -> begin
              let skel = match lf.Form.skel.form with
                | Atom (pol, p, _) -> atom pol p []
                | _ ->
                    Format.(
                      eprintf "[WEIRD] %a = %s@." (format_form ()) lf.skel lf.label.Idt.rep
                    ) ;
                    lf.skel
              in
              Some (lf.Form.label, (lf.label, skel))
            end
          | _ -> None
      end lforms
    in
    let ctx_particular =
      Sequent.to_list sq.left
      |> List.map (fun (p, ts) -> (next_local (), (p, atom (get_polarity ~lforms p) p ts)))
    in
    let goal = Seqproof.{
        term_vars = Idt.IdtMap.empty ;
        left_active = [] ;
        left_passive = ctx_particular @ ctx_ambient ;
        right = begin
          match sq.right with
          | None -> disj []
          | Some (p, ts) -> atom (get_polarity ~lforms p) p ts
        end
      } in
    Format.(
      eprintf "Reconstructing: @[%a@]@."
        Seqproof.format_sequent goal
    ) ;
    match Reconstruct.reconstruct (module Agencies.Rebuild)
            ~max:1 ~lforms ~goal
            ~cert:sq.skel
    with
    | Some (prf :: _) ->
        Config.pprintf "<p>Found: <code>%a</code></p>@."
          Seqproof.format_seqproof prf ;
        if List.mem `check __paranoia then begin
          Seqproof_print.print prf ~lforms ~goal ;
          Config.pprintf "<hr>@."
        end
    | Some []
    | None ->
        Format.(eprintf "Could not reconstruct@.@[<v0>%a@]@." Seqproof.format_sequent goal) ;
        failwith "[PARANOIA] proof reconstruction failed"
  end

let noop () = ()

type result = {
  lforms  : lform list ;
  goal    : lform ;
  found   : Sequent.t ;
}

module Inv (D : Data) = struct

  exception Escape of result

  let inverse_method ?(left=[]) ?(pseudo=[]) ?(per_loop=noop) right =
    try
      D.reset () ;
      let rules = ref [] in
      let (lfs, goal_lf, gen) = Rule_gen.generate0 left pseudo right in
      let goal_seq = mk_sequent ~right:(goal_lf.label, goal_lf.args) () in
      (* Format.printf "Goal sequent: %a@." (Sequent.format_sequent ()) goal_seq ; *)
      let add_seq sq =
        if Sequent.subsume sq goal_seq then begin
          D.register sq ;
          (* Sequent.Test.print sq ; *)
          (* Format.printf "[%d] %a@." sq.sqid (Sequent.format_sequent ()) sq ; *)
          raise (Escape {lforms = lfs ;
                         goal = goal_lf ;
                         found = sq})
        end ;
        D.register sq ;
        paranoid_check ~lforms:lfs sq
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
    with Escape res -> Some res
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
    | Some res -> begin
        match
          Ft.to_list res.found.left |>
          List.Exceptionless.find (fun (p, _) -> Form.is_pseudo p)
        with
        | None -> Format.printf "Proved!@."
        | Some (p, _) -> Format.printf "UNSOUND: Used pseudo %s.@." p.rep
      end

  let rec s_n n x = match n with 0 -> x | n -> s (s_n (n - 1) x)

  let even x = Form.atom NEG (intern "even") [x]
  let even_theory = [ intern "evz", even z ;
                      intern "evs", forall_ "x" (fun x -> implies [even x] (even (s (s x)))) ]
  let even_prune n = [ intern "evp", forall_ "x" (fun x -> even (s_n n x)) ]
  let even_prune n = [ ]
  let even_right = even (s_n 2 z) |> shift
  let even_test n = inverse_test ~theory:even_theory ~pseudo:even_prune ~goal:even_right n

  let odd x = Form.atom NEG (intern "odd") [x]
  let odd_theory = [ intern "od1", odd (s z) ;
                     intern "ods", forall_ "x" (fun x -> implies [odd (s_n 2 x)] (odd x)) ]
  let odd_prune_unguarded n = [
    intern "odp", (forall_ "x" (fun x -> odd (s_n n x)))
  ]
  let odd_prune_guarded n = [
    intern "odpg", 
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
  let bal_th = [ intern "balz", bal lf z ;
                 intern "bals", forall_ "x"
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
    [ intern "balp", spin (idx 1) n ]
  let bal_right = exists (intern "x") (bal (nd lf (nd lf lf)) (idx 0))
  let bal_test n = inverse_test ~theory:bal_th ~pseudo:bal_prune ~goal:bal_right n

end
