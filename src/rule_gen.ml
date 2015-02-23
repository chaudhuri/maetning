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

let generate_rules ~sc lforms =
  let rec focus_right left right =
    match right.form with
    | Atom (POS, p, pargs) ->
        init p pargs
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
        init p pargs
    | And (NEG, f1, f2) ->
        focus_left left f1 ratm @ focus_left left f2 ratm
    | True NEG -> []
    | Implies (f1, f2) ->
        let left_rules = focus_left left f2 ratm in
        let right_rules = focus_right left f1 in
        binary_join left_rules right_rules
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

  and init p pargs =
    [{prems = [mk_sequent ()
                 ~left:(Ft.singleton (p, pargs))
                 ~right:(p, pargs)] ;
      concl = mk_sequent ()
                 ~left:(Ft.singleton (p, pargs))
                 ~right:(p, pargs) ;
      eigen = IdtSet.empty }]

  and binary_join left_rules right_rules =
    let rules = List.map begin
        fun left_rule ->
          List.map begin
            fun right_rule ->
              { prems = left_rule.prems @ right_rule.prems ;
                concl = mk_sequent ()
                    ~left:(Ft.append left_rule.concl.left right_rule.concl.left)
                    ?right:None ;
                eigen = IdtSet.union left_rule.eigen right_rule.eigen }
          end right_rules
      end left_rules in
    List.concat rules
  in
  let process_lform lf =
    match lf.place with
    | Left ->
        focus_left [] lf.skel None |>
        List.map begin fun rule ->
          {rule with
           concl = mk_sequent ()
               ~left:(Ft.snoc rule.concl.left (lf.label, lf.args))
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
  let filter_atoms place = List.filter_map begin
      fun lf ->
        if lf.place = place then Some (lf.label, lf.args)
        else None
    end atoms in
  let left_atoms = filter_atoms Left in
  let right_atoms = filter_atoms Right in
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

end
