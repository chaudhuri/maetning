(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* prover internals *)

open Batteries
open Debug

open Term
open Form
open Rule
open Sequent

let __paranoia = [
  (* `reconstruct ; *)
  (* `check ; *)
]

type 'a ts = {
  id : int ;
  th : 'a ;
}

module type Data = sig
  val reset : unit -> unit
  val register : Sequent.t -> unit
  val select : unit -> Sequent.t ts option
  val iter_active : (Sequent.t ts -> 'a) -> unit
  val print_statistics : unit -> unit
  val finish_initial : unit -> unit
end

module Trivial : Data = struct
  let sos : Sequent.t ts Deque.t ref = ref Deque.empty
  let active : Sequent.t ts list ref = ref []
  let db : Sequent.t ts list ref = ref []

  let sqidgen = new Namegen.namegen (fun n -> n)

  let reset () =
    sos := Deque.empty ;
    active := [] ;
    db := [] ;
    sqidgen#reset

  let finish_initial () = ()
    (* sos := Deque.rev !sos *)

  let subsumed sq =
    List.exists (fun old -> Sequent.subsume old.th sq) !db

  let index sq =
    let id = sqidgen#next in
    dprintf "index" "[%d] @[%a@]@." id (format_sequent ())
      (Sequent.replace_sequent ~repl:(Sequent.canonize sq) sq) ;
    dprintf "skeleton" "%a@." Skeleton.format_skeleton sq.skel ;
    let sqt = {id ; th = sq} in
    db := sqt :: !db ;
    sos := Deque.snoc !sos sqt

  let register sq =
    if not (subsumed sq) then index sq
    (* else dprintf "subsumption" "[%d] @[%a@]@." sq.sqid (format_sequent ()) sq *)

  let select () =
    match Deque.front !sos with
    | Some (sel, rest) ->
        sos := rest ;
        active := sel :: !active ;
        dprintf "select" "[%d] @[%a@]@." sel.id (format_sequent ()) sel.th ;
        let sel = {sel with th = Sequent.freshen sel.th ()} in
        dprintf "rename" "@[%a@]@." (format_sequent ()) sel.th ;
        Some sel
    | None -> None

  let iter_active doit =
    List.iter begin fun act ->
        let act = {act with th = Sequent.freshen act.th ()} in
        doit act |> ignore
    end !active

  let print_statistics () =
    dprintf "stats" "@[<v0>#active = %d@,#db = %d@]@." (List.length !active) (List.length !db)
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
  match List.find (fun oldrr -> Rule.rule_subsumes oldrr.th rr) rules with
  | oldrr ->
      dprintf "rulesub" "@[<v0>Rule @[%a@]@,Subs @[%a@]@]@."
        (format_rule ()) oldrr.th
        (format_rule ()) rr ;
      false
  | exception Not_found -> true

let ruleidgen = new Namegen.namegen (fun n -> n)

let rec percolate0 ~sc_fact ~sc_rule ~sel ~iter rules =
  let new_rules = percolate_once ~sc_fact ~iter:(fun doit -> doit sel) rules in
  List.iter sc_rule new_rules ;
  if new_rules <> [] then percolate1 ~sc_fact ~sc_rule ~iter new_rules

and percolate1 ~sc_fact ~sc_rule ~iter rules =
  let new_rules = percolate_once ~sc_fact ~iter rules in
  (* List.iter sc_rule new_rules ; *)
  if new_rules <> [] then percolate1 ~sc_fact ~sc_rule ~iter new_rules

and percolate_once ~sc_fact ~iter rules =
  let new_rules : rule ts list ref = ref [] in
  let add_rule rr =
    match rr.prems with
    | [] -> sc_fact rr.concl
    | _ ->
        let rr = Rule.freshen rr in
        if is_new_rule_wrt !new_rules rr &&
           is_new_rule_wrt rules rr
        then new_rules := {id = ruleidgen#next ; th = rr} :: !new_rules
  in
  List.iter begin fun rr ->
    iter begin fun sq ->
      let sq0 = sq in
      let rr0 = rr in
      (* if sq0.ts < rr0.ts then *)
      (*   dprintf "rulefilter" "@[<v0>Dropping [%d:%d] @[%a@]@,Against [:%d] rule @[%a@]@]@." *)
      (*     sq.id sq.ts (format_sequent ()) sq0.th *)
      (*     rr.ts (format_rule ()) rr0.th *)
      (* else *)
      Rule.specialize_default rr.th sq.th
        ~sc_fact:(fun sq ->
            dprintf "factgen" "@[<v0>Trying [%d] @[%a@]@,With [%d] @[%a@]@,Produced @[%a@]@]@."
              sq0.id (format_sequent ()) sq0.th
              rr0.id (format_rule ()) rr0.th
              (format_sequent ()) sq ;
            sc_fact sq
          )
        ~sc_rule:(fun rr ->
            dprintf "rulegen" "@[<v0>Trying [%d] @[%a@]@,With [%d] @[%a@]@,Produced rule @[%a@]@]@."
              sq0.id (format_sequent ()) sq0.th
              rr0.id (format_rule ()) rr0.th
              (format_rule ()) rr ;
            add_rule rr
          )
    end
  end rules ;
  !new_rules

let get_polarity ~lforms p =
  match List.find (fun lf -> lf.label == p) lforms with
  | lf -> polarity lf.skel
  | exception Not_found ->
      lookup_polarity p

let rec freeze_vars t =
  match t.term with
  | Var v -> app (Idt.intern (v.Idt.rep ^ "¶")) []
  | App (f, ts) -> app f (List.map freeze_vars ts)
  | Idx n -> t

let rec freeze_vars_form f =
  match f.form with
  | Atom (pol, p, ts) -> atom pol p (List.map freeze_vars ts)
  | And (pol, f, g) -> conj ~pol [freeze_vars_form f ; freeze_vars_form g]
  | True pol -> conj ~pol []
  | Or (f, g) -> disj [freeze_vars_form f ; freeze_vars_form g]
  | False -> disj []
  | Implies (f, g) -> implies [freeze_vars_form f] (freeze_vars_form g)
  | Exists (x, f) -> exists x (freeze_vars_form f)
  | Forall (x, f) -> forall x (freeze_vars_form f)
  | Shift f -> shift (freeze_vars_form f)

let paranoid_check ~lforms sq =
  if List.mem `reconstruct __paranoia then begin
    (* Seqproof.hypgen#reset ; *)
    let next_local =
      let current = ref 0 in
      fun () -> incr current ; Idt.intern ("v" ^ string_of_int !current)
    in
    let ctx_ambient = List.filter_map begin
        fun lf -> match lf.place with
          | Left Global ->
              Some (lf.label, (lf.label, freeze_vars_form lf.Form.skel))
          | Left Pseudo -> begin
              let skel = match lf.Form.skel.form with
                | Atom (pol, p, _) -> atom pol p []
                | _ ->
                    Format.(
                      eprintf "[WEIRD] %a = %s@." (format_form ()) lf.skel lf.label.Idt.rep
                    ) ;
                    lf.skel
              in
              Some (lf.Form.label, (lf.label, freeze_vars_form skel))
            end
          | _ -> None
      end lforms
    in
    let ctx_particular =
      Sequent.to_list sq.left
      |> List.map (fun (p, ts) -> (next_local (), (p, atom (get_polarity ~lforms p) p (List.map freeze_vars ts))))
    in
    let goal = Seqproof.{
        term_vars = Idt.IdtMap.empty ;
        left_active = [] ;
        left_passive = ctx_particular @ ctx_ambient ;
        right = begin
          match sq.right with
          | None -> disj []
          | Some (p, ts) -> atom (get_polarity ~lforms p) p (List.map freeze_vars ts)
        end
      } in
    dprintf "paranoia" "Reconstructing: @[%a@]@." Seqproof.format_sequent goal ;
    match Reconstruct.reconstruct (module Agencies.Rebuild)
            ~max:1 ~lforms ~goal
            ~cert:sq.skel
    with
    | Some prf ->
        Config.pprintf "<p>Paranoia for <code>%a</code></p>@." (format_sequent ()) sq ;
        Config.pprintf "<p>Found: <code>%a</code></p>@."
          Seqproof.format_seqproof prf ;
        if List.mem `check __paranoia then begin
          Seqproof_print.print prf ~lforms ~goal ;
          Config.pprintf "<hr>@."
        end
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
      ruleidgen#reset ;
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
        match rr.th.prems with
        | [] ->  add_seq rr.th.concl
        | _ ->
            let rr = {rr with th = Rule.freshen rr.th} in
            if not @@ List.exists (fun oldrr -> Rule.rule_subsumes oldrr.th rr.th) !rules then begin
              dprintf "rule" "[%d] @[%a@]@." rr.id (format_rule ()) rr.th ;
              rules := rr :: !rules
            end
      in
      gen ~sc:(fun rr -> add_rule {id = ruleidgen#next ; th = rr}) ;
      D.finish_initial () ;
      dprintf "rule" "  ****************************************@." ;
      spin_until_none D.select begin fun sel ->
        percolate0 !rules ~sel ~iter:D.iter_active ~sc_rule:add_rule ~sc_fact:add_seq ;
        D.print_statistics () ;
        per_loop () ;
      end ;
      None
    with Escape res ->
      Some res
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
