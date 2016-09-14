(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* prover internals *)

open Batteries
open Debug

open Idt
open Term
open Form
open Rule
open Sequent

type 'a ts = {
  id : int ;
  th : 'a ;
}

module type Data = sig
  val reset : unit -> unit
  val register : Sequent.t -> unit
  val select : unit -> Sequent.t ts option
  val subsumes : ?all:bool -> Sequent.t -> bool
  val iter_active : (Sequent.t ts -> 'a) -> unit
  val iter_known : (Sequent.t ts -> 'a) -> unit
  val print_statistics : unit -> unit
  val finish_initial : unit -> unit
end

module Trivial : Data = struct
  module Ints = Set.Make(Int)

  let sos : Sequent.t ts Deque.t ref = ref Deque.empty
  let active : (int, Sequent.t ts) Hashtbl.t = Hashtbl.create 19
  let db : (int, Sequent.t ts) Hashtbl.t = Hashtbl.create 19
  let concs : (int, Ints.t) Hashtbl.t = Hashtbl.create 19
  let kills : (int, unit) Hashtbl.t = Hashtbl.create 19

  let sqidgen = new Namegen.namegen (fun n -> n)

  let reset () =
    sos := Deque.empty ;
    Hashtbl.clear active ;
    Hashtbl.clear db ;
    Hashtbl.clear concs ;
    Hashtbl.clear kills ;
    sqidgen#reset

  let finish_initial () = ()
    (* sos := Deque.rev !sos *)

  let subsumes ?(all=false) sq =
    try
      Hashtbl.iter begin
        fun sqid old ->
          if (all || not (Hashtbl.mem kills sqid)) && Sequent.subsume old.th sq then
            raise Not_found
      end db ; false
    with Not_found -> true

  let sos_subsumes sq =
    Deque.find (fun old -> not (Hashtbl.mem kills old.id) && Sequent.subsume old.th sq) !sos
    |> Option.is_some

  let index sq =
    let id = sqidgen#next in
    dprintf "index" "[%d] @[%a@]@." id Sequent.format_canonical sq ;
    dprintf "skeleton" "%a@." Skeleton.format_skeleton sq.skel ;
    (* let sq = Sequent.freshen sq () in *)
    let sqt = {id ; th = sq} in
    Hashtbl.replace db id sqt ;
    ISet.iter begin fun ancid ->
      match Hashtbl.find concs ancid with
      | cs -> Hashtbl.replace concs ancid (Ints.add id cs)
      | exception Not_found -> Hashtbl.add concs ancid (Ints.singleton id)
    end sq.ancs ;
    sos := Deque.snoc !sos sqt ;
    sqt

  let register sq =
    if subsumes sq then () else
    let sqt = index sq in
    let tokill = Hashtbl.fold begin
      fun _ old tokill ->
        if sqt.id <> old.id && not (Hashtbl.mem kills old.id) && Sequent.subsume sqt.th old.th
        then Ints.add old.id tokill
        else tokill
    end db Ints.empty in
    let rec spin wl =
      match Ints.pop wl with
      | (ksqid, wl) ->
          if ksqid == sqt.id then spin wl else begin
            Hashtbl.replace kills ksqid () ;
            let oldsq = Hashtbl.find db ksqid in
            (* Hashtbl.remove db ksqid ; *)
            Hashtbl.remove active ksqid ;
            dprintf "backsub" "[%d] @[%a@]@." ksqid (format_sequent ()) oldsq.th ;
            let wl =
              match Hashtbl.find concs ksqid with
              | ksqcons ->
                  let ksqcons = Ints.filter (fun id -> not @@ Hashtbl.mem kills id) ksqcons in
                  Hashtbl.replace concs ksqid ksqcons ;
                  (* dprintf "backsub" "Will also kill: [%s]@." *)
                  (*   (Ints.to_list ksqcons |> List.map string_of_int |> String.concat ",") ; *)
                  Ints.union ksqcons wl
              | exception Not_found -> wl
            in
            spin wl
          end
      | exception Not_found -> ()
    in
    spin tokill

  let rec select () =
    match Deque.front !sos with
    | Some (sel, rest) ->
        sos := rest ;
        (* Jeez Rick, backsubbed sequents in the SOS are still alive! You can't just kill them! *)
        (* Y-y-y-y-you may cease to exist! *)
        let rsel = {sel with th = Sequent.freshen sel.th ()} in
        if sos_subsumes rsel.th then select () else begin
          Hashtbl.add active sel.id sel ;
          dprintf "select" "[%d] @[%a@]@." sel.id (format_sequent ()) sel.th ;
          dprintf "rename" "@[%a@]@." (format_sequent ()) rsel.th ;
          Some rsel
        end
    | None -> None

  let iter_active doit =
    Hashtbl.iter begin fun id act ->
      if Hashtbl.mem kills id then () else
      let act = {act with th = Sequent.freshen act.th ()} in
      doit act |> ignore
    end active

  let iter_known doit =
    let doit sqt = ignore (doit sqt) in
    iter_active doit ;
    Deque.iter doit !sos

  let print_statistics () =
    dprintf "stats" "@[<v0>#active = %d@,#db = %d@]@." (Hashtbl.length active) (Hashtbl.length db)
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

let is_new_rule (module D : Data) rr =
  not @@ D.subsumes rr.concl

let ruleidgen = new Namegen.namegen (fun n -> n)

let rec percolate0 (module D : Data) ~sc_fact ~sc_rule ~sel ~iter rules =
  let new_rules = percolate_once ~spec:Rule.specialize_any (module D : Data) ~sc_fact ~iter:(fun doit -> doit sel) rules in
  List.iter sc_rule new_rules ;
  if new_rules <> [] then percolate1 (module D : Data) ~sc_fact ~sc_rule ~iter new_rules

and percolate1 (module D : Data) ~sc_fact ~sc_rule ~iter rules =
  let new_rules = percolate_once (module D : Data) ~sc_fact ~iter rules in
  (******************************************************************************)
  (*                                                                            *)
  (*                   List.iter sc_rule new_rules ;                            *)
  (*                                                                            *)
  (* No point remembering these rules as they will never be constructed again.  *)
  (* Each percolate0 constructs a globally new family of percolating rules      *)
  (******************************************************************************)
  if new_rules <> [] then percolate1 (module D : Data) ~sc_fact ~sc_rule ~iter new_rules

and percolate_once (module D : Data) ?spec ~sc_fact ~iter rules =
  let new_rules : rule ts list ref = ref [] in
  let add_rule rr =
    match rr.prems with
    | [] -> sc_fact rr.concl
    | _ ->
        let rr = Rule.freshen rr in
        if is_new_rule (module D) rr then begin
          let id = ruleidgen#next in
          dprintf "rulegen" "It was given number [%d]@." id ;
          new_rules := {id ; th = rr} :: !new_rules
        end
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
      (* dprintf "percolate" "@[<v0>Trying [%d] @[%a@]@,With [%d] @[%a@]@." *)
      (*   sq0.id (format_sequent ()) sq0.th *)
      (*   rr0.id (format_rule ()) rr0.th ; *)
      Rule.specialize_default ?spec rr.th (sq.id, sq.th)
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
  match IdtMap.find p lforms with
  | lf -> polarity lf.Form.skel
  | exception Not_found -> lookup_polarity p

let rec freeze_vars t =
  match t.term with
  | Var v -> app (Idt.intern (var_to_string v ^ "¶")) []
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
  if !Config.paranoia then begin
    (* Seqproof.hypgen#reset ; *)
    let next_local =
      let current = ref 0 in
      fun () -> incr current ; Idt.intern ("v" ^ string_of_int !current)
    in
    let ctx_ambient = List.filter_map begin fun (_, lf) ->
        match lf.place with
        | Left Global ->
            Some (lf.label, (lf.label, freeze_vars_form lf.Form.skel))
        | Left Pseudo -> begin
            let skel = match lf.Form.skel.form with
              | Atom (pol, p, _) -> atom pol p []
              | _ ->
                  Format.(
                    eprintf "[WEIRD] %a = %s@." format_form lf.Form.skel lf.label.Idt.rep
                  ) ;
                  lf.Form.skel
            in
            Some (lf.Form.label, (lf.label, freeze_vars_form skel))
          end
        | _ -> None
      end (IdtMap.bindings lforms)
    in
    let ctx_particular =
      Sequent.to_list sq.left
      |> List.map (fun (p, ts) -> (next_local (), (p, atom (get_polarity ~lforms p) p (List.map freeze_vars ts))))
    in
    let goal = Seqproof.{
        term_vars = Idt.IdtMap.empty ;
        left_active = [] ;
        left_passive = IdtMap.digest (ctx_particular @ ctx_ambient) ;
        right = begin
          match sq.Sequent.right with
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
        if Config.print_paranoia then begin
          Seqproof_print.print prf ~lforms ~goal ;
          Config.pprintf "<hr>@."
        end
    | None ->
        Format.(eprintf "Could not reconstruct@.@[<v0>%a@]@." Seqproof.format_sequent goal) ;
        failwith "[PARANOIA] proof reconstruction failed"
  end

let noop () = ()

type 'a result = {
  lforms  : lform IdtMap.t ;
  goal    : lform ;
  status  : 'a ;
}

module Inv (D : Data) = struct

  exception Escape of Sequent.t option result

  let inverse_method ?(left=[]) ?(pseudo=[]) ?(per_loop=noop) right =
    try
      D.reset () ;
      ruleidgen#reset ;
      let rules = ref [] in
      let (lfs, goal_lf, gen) = Rule_gen.generate0 left pseudo right in
      let goal_seq = mk_sequent ~right:(goal_lf.label, goal_lf.args) () in
      (* Format.printf "Goal sequent: %a@." (Sequent.format_sequent ()) goal_seq ; *)
      let add_seq sq =
        D.register sq ;
        if Sequent.subsume sq goal_seq then begin
          raise (Escape {lforms = lfs ;
                         goal = goal_lf ;
                         status = Some sq})
        end ;
        paranoid_check ~lforms:lfs sq
      in
      let add_rule rr =
        match rr.th.prems with
        | [] ->  add_seq rr.th.concl
        | _ -> begin
            let rr = {rr with th = Rule.freshen rr.th} in
            match List.find (fun oldrr -> Rule.rule_subsumes oldrr.th rr.th) !rules with
            | oldrr ->
                dprintf "rulegen" "But it was subsumed by: [%d] @[%a@]@."
                  oldrr.id (format_rule ()) oldrr.th
            | exception Not_found ->
                dprintf "rule" "[%d] @[%a@]@." rr.id (format_rule ()) rr.th ;
                rules := rr :: !rules
          end
      in
      gen ~sc:(fun rr -> add_rule {id = ruleidgen#next ; th = rr}) ;
      D.finish_initial () ;
      dprintf "rule" "  ****************************************@." ;
      spin_until_none D.select begin fun sel ->
        percolate0 (module D) !rules ~sel ~iter:D.iter_active ~sc_rule:add_rule ~sc_fact:add_seq ;
        D.print_statistics () ;
        per_loop () ;
      end ;
      {lforms = lfs ; goal = goal_lf ; status = None}
    with Escape res -> res
end

module Data = Trivial
include Inv(Data)

module Test () = struct
  open Idt
  module T = Rule_gen.Test ()
  open T


  let sleep n () =
    Format.printf "One loop done@." ;
    Unix.sleep n

  let inverse_test ~theory ~pseudo ~goal ?(per_loop=noop) n =
    let res = inverse_method ~left:theory ~pseudo:(pseudo n) ~per_loop goal in
    match res.status with
    | None ->
        Format.printf "Not provable@."
    | Some resq -> begin
        match
          Ft.to_list resq.left |>
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
