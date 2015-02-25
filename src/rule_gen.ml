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
  [{prems = [] ;
    concl = mk_sequent () ~left:(Ft.singleton (p, pargs)) ;
    eigen = IdtSet.empty }]

and left_init p pargs =
  [{prems = [] ;
    concl = mk_sequent () ~right:(p, pargs) ;
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

let vars_rule rr =
  (* let repls_prems = List.map Sequent.freshen_ rr.prems |> List.map fst in *)
  let repl_concl = Sequent.freshen_ rr.concl |> fst in
  let vs = IdtMap.fold (fun v _ vs -> IdtSet.add v vs) repl_concl IdtSet.empty in
  (* let vs = List.fold_left begin fun vs repl_prem -> *)
  (*     IdtMap.fold (fun v _ vs -> IdtSet.add v vs) repl_prem vs *)
  (*   end vs repls_prems in *)
  List.map var (IdtSet.elements vs)

let generate_rules ~sc lforms =
  let process_lform lf =
    match lf.place with
    | Left lfp ->
        focus_left [] lf.skel None |>
        List.map begin fun rule ->
          let left =
            if lfp = Global
            then rule.concl.left
            else Ft.snoc rule.concl.left (lf.label, lf.args @ vars_rule rule)
          in
          {rule with
           concl = mk_sequent () ~left ?right:rule.concl.right}
        end
    | Right ->
        focus_right [] lf.skel |>
        List.map begin fun rule ->
          {rule with
           concl = mk_sequent ()
             ~left:rule.concl.left
             ~right:(lf.label, lf.args)}
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

let generate0 left pseudo right =
  assert (List.for_all (fun l -> polarity l = NEG) left) ;
  assert (List.for_all (fun l -> polarity l = NEG) pseudo) ;
  assert (polarity right = POS) ;
  let lforms = ref [] in
  let process place hyps =
    List.iter begin
      fun f ->
        let lfs = relabel ~place f in
        lforms := lfs @ !lforms
    end hyps in
  process (Left Global) left ;
  process (Left Pseudo) pseudo ;
  process Right [right] ;
  let goal_lform = List.hd !lforms in
  Format.(
    printf "Labeled formulas:@." ;
    List.iter (printf "  %a@." format_lform) !lforms ;
    printf "Goal is %s@." goal_lform.label.rep ;
  ) ;
  (goal_lform, generate_rules !lforms)

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
    let lforms = Form.Test.test f in
    generate_rules lforms ~sc:Rule.Test.print

end
