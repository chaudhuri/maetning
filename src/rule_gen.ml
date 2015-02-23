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
open Sequent
open Rule

let rec focus_right left right =
  match right.form with
  | Atom (POS, p, pargs) ->
      right_init p pargs
  | And (POS, f1, f2) ->
      let left_rules = focus_right left f1 in
      let right_rules = focus_right left f2 in
      binary_join left_rules right_rules
  | True POS ->
      [{ prems = [] ;
         concl = mk_sequent () ;
         eigen = IdtSet.empty }]
  | Or (f1, f2) ->
      focus_right left f1 @ focus_right left f2
  | False -> []
  | Exists (_, f) ->
      let v = fresh_var `evar in
      let f = app_form (Cons (Shift 0, v)) f in
      focus_right left f
  | Shift f ->
      active_right left [] f
  | Atom (NEG, _, _)
  | And (NEG, _, _)
  | True NEG
  | Forall _
  | Implies _ ->
      assert false

and focus_left left lfoc ratm =
  match lfoc.form with
  | Atom (NEG, p, pargs) ->
      left_init p pargs
  | And (NEG, f1, f2) ->
      focus_left left f1 ratm @ focus_left left f2 ratm
  | True NEG -> []
  | Implies (f1, f2) ->
      let left_rules = focus_left left f2 ratm in
      let right_rules = focus_right left f1 in
      binary_join ~right_selector:`left left_rules right_rules
  | Forall (_, f) ->
      let v = fresh_var `evar in
      let f = app_form (Cons (Shift 0, v)) f in
      focus_left left f ratm
  | Shift f ->
      active_left left [f] ratm
  | Atom (POS, _, _)
  | And (POS, _, _)
  | True POS
  | Or _ | False | Exists _ ->
      Format.(fprintf err_formatter
                "Cannot left-focus on %a@."
                (format_form ()) lfoc) ;
      assert false

and active_right left_passive left_active right =
  match right.form with
  | Atom (NEG, p, pargs) ->
      active_left left_passive left_active (Some (p, pargs))
  | And (NEG, f1, f2) ->
      let left_rules = active_right left_passive left_active f1 in
      let right_rules = active_right left_passive left_active f2 in
      binary_join left_rules right_rules
  | True NEG ->
      [{ prems = [] ;
         concl = mk_sequent () ;
         eigen = IdtSet.empty }]
  | Implies (f, g) ->
      active_right left_passive (f :: left_active) g
  | Forall (_, f) ->
      let v = fresh_var `param in
      let f = app_form (Cons (Shift 0, v)) f in
      let rules = active_right left_passive left_active f in
      let ev = IdtSet.singleton (unvar v) in
      List.map (fun r -> { r with eigen = IdtSet.union r.eigen ev }) rules
  | Shift {form = Atom (POS, p, pargs) ; _} ->
      active_left left_passive left_active (Some (p, pargs))
  | Atom (POS, _, _)
  | And (POS, _, _)
  | True POS
  | Or _ | False | Exists _
  | Shift _ ->
      assert false

and active_left left_passive left_active ratm =
  match left_active with
  | [] ->
      [{ prems = [mk_sequent ()
                    ~left:(Ft.of_list left_passive)
                    ?right:ratm] ;
         concl = mk_sequent () ;
         eigen = IdtSet.empty }]
  | la :: left_active ->
      active_left_one left_passive left_active la ratm

and active_left_one left_passive left_active la ratm =
  match la.form with
  | Atom (POS, p, pargs) ->
      active_left ((p, pargs) :: left_passive) left_active ratm
  | Shift {form = Atom (NEG, p, pargs) ; _} ->
      active_left ((p, pargs) :: left_passive) left_active ratm
  | And (POS, f1, f2) ->
      active_left left_passive (f1 :: f2 :: left_active) ratm
  | True POS ->
      active_left left_passive left_active ratm
  | Or (f1, f2) ->
      let left_rules = active_left left_passive (f1 :: left_active) ratm in
      let right_rules = active_left left_passive (f2 :: left_active) ratm in
      binary_join left_rules right_rules
  | False ->
      [{prems = [] ; concl = mk_sequent () ; eigen = IdtSet.empty}]
  | Exists (_, f) ->
      let v = fresh_var `param in
      let f = app_form (Cons (Shift 0, v)) f in
      let rules = active_left left_passive (f :: left_active) ratm in
      let ev = IdtSet.singleton (unvar v) in
      List.map (fun r -> { r with eigen = IdtSet.union r.eigen ev }) rules
  | Atom (NEG, _, _)
  | And (NEG, _, _)
  | True NEG
  | Implies _
  | Forall _
  | Shift _ ->
      assert false

and right_init p pargs =
  [{prems = [] (* [mk_sequent () *)
            (*    ~left:(Ft.singleton (p, pargs)) *)
            (*    ~right:(p, pargs)] *) ;
    concl = mk_sequent ()
        ~left:(Ft.singleton (p, pargs)) ;
    eigen = IdtSet.empty }]

and left_init p pargs =
  [{prems = [] (* [mk_sequent () *)
    (*    ~left:(Ft.singleton (p, pargs)) *)
    (*    ~right:(p, pargs)] *) ;
    concl = mk_sequent ()
        ~right:(p, pargs) ;
    eigen = IdtSet.empty }]

and binary_join ?(right_selector=`none) left_rules right_rules =
  let rules = List.map begin
      fun left_rule ->
        List.map begin
          fun right_rule ->
            let right = match right_selector with
              | `left -> left_rule.concl.right
              | `right -> right_rule.concl.right
              | `none -> None
            in
            { prems = left_rule.prems @ right_rule.prems ;
              concl = mk_sequent ()
                  ~left:(Ft.append left_rule.concl.left right_rule.concl.left)
                  ?right ;
              eigen = IdtSet.union left_rule.eigen right_rule.eigen }
        end right_rules
    end left_rules in
  List.concat rules

let generate_rules ~sc lforms =
  let process_lform lf =
    match lf.place with
    | Left lfp ->
        focus_left [] lf.skel None |>
        List.map begin fun rule ->
          let left =
            if lfp = Global
            then rule.concl.left
            else Ft.snoc rule.concl.left (lf.label, lf.args)
          in
          {rule with
           concl = mk_sequent () ~left
               ?right:rule.concl.right
               ~inits:rule.concl.inits}
        end
    | Right ->
        focus_right [] lf.skel |>
        List.map begin fun rule ->
          {rule with
           concl = mk_sequent ()
             ~left:rule.concl.left
             ~right:(lf.label, lf.args)
             ~inits:rule.concl.inits}
        end
  in
  let rules_list = List.map process_lform lforms in
  List.iter (fun rules -> List.iter sc rules) rules_list

let freshen_atom lf =
  let (_, f0) = Term.freshen ~repl:IdtMap.empty (app lf.label lf.args) in
  match f0.term with
  | App (_, args) ->
      {lf with args = args}
  | _ -> assert false

let generate_initials ~sc atoms =
  let filter_atoms test = List.filter_map begin
      fun lf ->
        if test lf.place then Some (lf.label, lf.args)
        else None
    end atoms in
  let left_atoms = filter_atoms (function Left _ -> true | _ -> false) in
  let right_atoms = filter_atoms (function Right -> true | _ -> false) in
  List.iter begin fun (p, pargs) ->
    List.iter begin fun (q, qargs) ->
      if p != q then () else
      try
        let (repl, args) = Unify.unite_lists IdtMap.empty pargs qargs in
        mk_sequent ()
          ~left:(Ft.singleton (p, args))
          ~right:(p, args) |> sc
      with
      Unify.Unif _ -> ()
    end right_atoms
  end left_atoms

let generate0 ~sc_rules ~sc_inits left pseudo right =
  assert (List.for_all (fun l -> polarity l = NEG) left) ;
  assert (List.for_all (fun l -> polarity l = NEG) pseudo) ;
  assert (polarity right = POS) ;
  let atoms = ref [] in
  let lforms = ref [] in
  let process place hyps =
    List.iter begin
      fun f ->
        let (lfs, ats) = relabel ~place f in
        if place <> Left Pseudo then
          atoms := ats @ !atoms ;
        lforms := lfs @ !lforms
    end hyps in
  process (Left Global) left ;
  process (Left Pseudo) pseudo ;
  process Right [right] ;
  let goal_lform = List.hd !lforms in
  Format.(
    printf "Labeled formulas:@." ;
    List.iter (printf "  %a@." format_lform) !lforms ;
    (* fprintf std_formatter "Atoms:@." ; *)
    (* List.iter (eprintf "%a@." format_lform) !atoms ; *)
    printf "Goal is %s@." goal_lform.label.rep ;
  ) ;
  generate_rules !lforms ~sc:sc_rules ;
  generate_initials (List.map freshen_atom !atoms) ~sc:sc_inits ;
  goal_lform

module Test = struct

  let p x y = Form.atom POS (intern "p") [x ; y]
  let q x = Form.atom POS (intern "q") [x]
  let a = Form.atom POS (intern "A") []
  let b = Form.atom POS (intern "B") []
  let c = Form.atom POS (intern "C") []
  let d = Form.atom POS (intern "D") []
  let z = Term.app (intern "z") []
  let s x = Term.app (intern "s") [x]

  let f0 = implies [disj [a ; b]] c
  let f1 = conj ~pol:NEG [implies [a] c ; implies [b] c]

  let test f =
    let (lforms, atoms) = Form.Test.test f in
    let atoms = List.map freshen_atom atoms in
    generate_rules lforms ~sc:Rule.Test.print ;
    generate_initials atoms ~sc:Sequent.Test.print

  let even x = Form.atom NEG (intern "even") [x]
  let even_theory = [ even z ;
                      forall (intern "x") (implies [even (idx 0)] (even (s (s (idx 0))))) ]
  let even_prune n =
    let rec prune_t t = function
      | 0 -> forall (intern "x") (even t)
      | n -> prune_t (s t) (n - 1)
    in [ prune_t (idx 0) n ]
  let even_right = even (s (s (s z))) |> shift

  let rec quiescently measure op =
    let before = measure () in
    op () ;
    let after = measure () in
    if before <> after then quiescently measure op

  exception Escape of Sequent.t

  let inverse_method ?(left=[]) ?(pseudo=[]) right =
    try begin
      let sos = ref [] in
      let rules = ref [] in
      let add_seq_initial sq =
        if List.exists (fun oldseq -> subsume oldseq sq) !sos then ()
        else sos := sq :: List.filter (fun oldseq -> not @@ subsume sq oldseq) !sos
      in
      let add_rule add_seq rr =
        if rr.prems = [] then add_seq rr.concl
        else begin
          (* Rule.Test.print rr ; *)
          rules := rr :: !rules
        end
      in
      let goal_lf = generate0 left pseudo right
          ~sc_rules:(add_rule add_seq_initial)
          ~sc_inits:add_seq_initial in
      let goal_seq = mk_sequent ~right:(goal_lf.label, goal_lf.args) () in
      List.iter Sequent.Test.print !sos ;
      let active = ref [] in
      while !sos <> [] do
        (* Format.printf "%d left in SOS@." (List.length !sos) ; *)
        let sel = List.hd !sos in
        (* Format.printf "Selected: %a@." (format_sequent ()) sel ; *)
        sos := List.tl !sos ;
        active := sel :: !active ;
        let add_seq sq =
          if List.exists (fun oldseq -> subsume oldseq sq) (!sos @ !active) then ()
          else begin
            Sequent.Test.print sq ;
            if subsume sq goal_seq then raise (Escape sq) ;
            sos := sq :: !sos
          end
        in
        List.iter begin fun rr ->
          Rule.specialize_default rr (Sequent.freshen sel ())
            ~sc_rule:(add_rule add_seq)
            ~sc_fact:add_seq
        end !rules ;
        quiescently (fun () -> List.length !rules)
          (fun () ->
             List.iter begin fun rr ->
               List.iter begin fun act ->
                 Rule.specialize_default rr (Sequent.freshen act ())
                   ~sc_rule:(add_rule add_seq)
                   ~sc_fact:add_seq
               end !active
             end !rules
          ) ;
      done ;
      None
    end with
    Escape sq ->
        (* Format.printf "Found derivation of:@.%a@." (format_sequent ()) sq ; *)
        Some sq

  let gtest n =
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

end
