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
open Skeleton
open Sequent
open Rule

let skel_map skf rrs =
  List.map begin fun rr ->
    {rr with concl = override rr.concl ~skel:(skf rr.concl.skel)}
  end rrs

let rec focus_right left right =
  match right.form with
  | Atom (POS, p, pargs) ->
      right_init p pargs
  | And (POS, f1, f2) ->
      let left_rules = focus_right left f1 in
      let right_rules = focus_right left f2 in
      binary_join left_rules right_rules
        (fun sk1 sk2 -> TensR (sk1, sk2))
  | True POS ->
      [{ prems = [] ;
         concl = mk_sequent () ~skel:OneR ;
         eigen = IdtSet.empty }]
  | Or (f1, f2) ->
      skel_map (fun sk -> PlusR1 sk) (focus_right left f1)
      @
      skel_map (fun sk -> PlusR2 sk) (focus_right left f2)
  | False -> []
  | Exists (_, f) ->
      let v = vargen#next `evar in
      let f = app_form (Cons (Shift 0, v)) f in
      skel_map (fun sk -> ExR sk) (focus_right left f)
  | Shift f ->
      skel_map (fun sk -> BlurR sk) (active_right left [] f)
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
      skel_map (fun sk -> WithL1 sk) (focus_left left f1 ratm)
      @
      skel_map (fun sk -> WithL2 sk) (focus_left left f2 ratm)
  | True NEG -> []
  | Implies (f1, f2) ->
      let left_rules = focus_left left f2 ratm in
      let right_rules = focus_right left f1 in
      binary_join ~right_selector:`left left_rules right_rules
        (fun sk1 sk2 -> ImpL (sk2, sk1))
  | Forall (_, f) ->
      let v = vargen#next `evar in
      let f = app_form (Cons (Shift 0, v)) f in
      skel_map (fun sk -> AllL sk)
        (focus_left left f ratm)
  | Shift f ->
      skel_map (fun sk -> BlurL sk)
        (active_left left [f] ratm)
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
        (fun sk1 sk2 -> WithR (sk1, sk2))
  | True NEG ->
      [{ prems = [] ;
         concl = mk_sequent () ~skel:TopR ;
         eigen = IdtSet.empty }]
  | Implies (f, g) ->
      skel_map (fun sk -> ImpR sk)
        (active_right left_passive (f :: left_active) g)
  | Forall (_, f) ->
      let v = vargen#next `param in
      let f = app_form (Cons (Shift 0, v)) f in
      let rules = active_right left_passive left_active f in
      let ev = IdtSet.singleton (unvar v) in
      List.map (fun r -> { r with eigen = IdtSet.union r.eigen ev }) rules
      |> skel_map (fun sk -> AllR sk)
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
      |> skel_map (fun sk -> Store sk)
  | Shift {form = Atom (NEG, p, pargs) ; _} ->
      active_left ((p, pargs) :: left_passive) left_active ratm
      |> skel_map (fun sk -> Store sk)
  | And (POS, f1, f2) ->
      active_left left_passive (f1 :: f2 :: left_active) ratm
      |> skel_map (fun sk -> TensL sk)
  | True POS ->
      active_left left_passive left_active ratm
      |> skel_map (fun sk -> OneL sk)
  | Or (f1, f2) ->
      let left_rules = active_left left_passive (f1 :: left_active) ratm in
      let right_rules = active_left left_passive (f2 :: left_active) ratm in
      binary_join left_rules right_rules
        (fun sk1 sk2 -> PlusL (sk1, sk2))
  | False ->
      [{prems = [] ; concl = mk_sequent () ~skel:ZeroL ; eigen = IdtSet.empty}]
  | Exists (_, f) ->
      let v = vargen#next `param in
      let f = app_form (Cons (Shift 0, v)) f in
      let rules = active_left left_passive (f :: left_active) ratm in
      let ev = IdtSet.singleton (unvar v) in
      List.map (fun r -> { r with eigen = IdtSet.union r.eigen ev }) rules
      |> skel_map (fun sk -> ExL sk)
  | Atom (NEG, _, _)
  | And (NEG, _, _)
  | True NEG
  | Implies _
  | Forall _
  | Shift _ ->
      assert false

and right_init p pargs =
  [{prems = [] ;
    concl = mk_sequent ()
        ~left:(Ft.singleton (p, pargs))
        ~skel:InitR ;
    eigen = IdtSet.empty }]

and left_init p pargs =
  [{prems = [] ;
    concl = mk_sequent ()
        ~right:(p, pargs)
        ~skel:InitL ;
    eigen = IdtSet.empty }]

and binary_join ?(right_selector=`none) left_rules right_rules mk_skel =
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
                  ~skel:(mk_skel left_rule.concl.skel right_rule.concl.skel)
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
            match lfp with
            | Global -> rule.concl.left
            | Local  -> Ft.snoc rule.concl.left (lf.label, lf.args)
            | Pseudo -> Ft.snoc rule.concl.left (lf.label, lf.args @ vars_rule rule)
          in
          let skel = FocL (lf.label, rule.concl.skel) in
          {rule with concl = override rule.concl ~left ~skel}
        end
    | Right ->
        focus_right [] lf.skel |>
        List.map begin fun rule ->
          let skel = FocR rule.concl.skel in
          {rule with
           concl = override rule.concl
               ~right:(Some (lf.label, lf.args))
               ~skel}
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
    printf "Labelled formulas:@." ;
    List.iter (printf "  %a.@." format_lform) !lforms ;
    printf "goal is %s.@." goal_lform.label.rep ;
  ) ;
  let expl ff =
    Format.(
      fprintf ff "%% setup@." ;
      List.iter (fprintf ff "%a.@." lp_lform) !lforms ;
      fprintf ff "%% goal@.%s.@." goal_lform.label.rep ;
    )
  in
  (!lforms, goal_lform, expl, generate_rules !lforms)

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
