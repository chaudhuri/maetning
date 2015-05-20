(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries
open Debug

open Idt
open Term
open Form
open Skeleton
open Sequent
open Rule

module S = VSet
module M = VMap

let skel_map skf rrs =
  List.map begin fun rr ->
    {rr with concl = override rr.concl ~skel:(skf rr.concl.skel)}
  end rrs

let add_fresh_extras ev rr =
  let extra = S.fold begin
      fun pv extra ->
        match M.find pv extra with
        | ts -> M.add pv (ev :: ts) extra
        | exception Not_found -> M.add pv [ev] extra
    end rr.eigen rr.extra in
  {rr with extra}

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
         eigen = S.empty ;
         extra = M.empty ;
         sats = [] ;
       }]
  | Or (f1, f2) ->
      skel_map (fun sk -> PlusR1 sk) (focus_right left f1)
      @
      skel_map (fun sk -> PlusR2 sk) (focus_right left f2)
  | False -> []
  | Exists (_, f) ->
      let v = vargen#next E in
      let f = app_form (Cons (Shift 0, v)) f in
      focus_right left f
      |> skel_map (fun sk -> ExR sk)
      |> List.map (add_fresh_extras v)
  | Shift f ->
      skel_map (fun sk -> BlurR sk) (active_right left [] f)
  | Atom (NEG, _, _)
  | And (NEG, _, _)
  | True NEG
  | Forall _
  | Implies _ ->
      Debug.bugf "Rule_gen.focus_right: negative: @[%a@]" (format_form ()) right

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
      let v = vargen#next E in
      let f = app_form (Cons (Shift 0, v)) f in
      focus_left left f ratm
      |> skel_map (fun sk -> AllL sk)
      |> List.map (add_fresh_extras v)
  | Shift f ->
      skel_map (fun sk -> BlurL sk)
        (active_left left [f] ratm)
  | Atom (POS, _, _)
  | And (POS, _, _)
  | True POS
  | Or _ | False | Exists _ ->
      Debug.bugf "Rule_gen.focus_left: positive: @[%a@]" (format_form ()) lfoc

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
         eigen = S.empty ;
         extra = M.empty ;
         sats = [] ;
       }]
  | Implies (f, g) ->
      skel_map (fun sk -> ImpR sk)
        (active_right left_passive (f :: left_active) g)
  | Forall (_, f) ->
      let vt = vargen#next U in
      let v = unvar vt in
      let f = app_form (Cons (Shift 0, vt)) f in
      active_right left_passive left_active f
      |> List.map (fun rr -> {rr with eigen = S.add v rr.eigen})
      |> skel_map (fun sk -> AllR sk)
  | Shift {form = Atom (POS, p, pargs) ; _} ->
      active_left left_passive left_active (Some (p, pargs))
  | Atom (POS, _, _)
  | And (POS, _, _)
  | True POS
  | Or _ | False | Exists _
  | Shift _ ->
      Debug.bugf "Rule_gen.active_right: positive: @[%a@]" (format_form ()) right

and active_left left_passive left_active ratm =
  match left_active with
  | [] ->
      let skel = Prem premidgen#next in
      [{ prems = [mk_sequent ()
                    ~skel
                    ~left:(Ft.of_list left_passive)
                    ?right:ratm, `extract] ;
         concl = mk_sequent ~skel () ;
         eigen = S.empty ;
         extra = M.empty ;
         sats = [] ;
       }]
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
      [{prems = [] ; concl = mk_sequent () ~skel:ZeroL ;
        eigen = S.empty ; extra = M.empty ; sats = []}]
  | Exists (_, f) ->
      let vt = vargen#next U in
      let v = unvar vt in
      let f = app_form (Cons (Shift 0, vt)) f in
      active_left left_passive (f :: left_active) ratm
      |> List.map (fun rr -> {rr with eigen = S.add v rr.eigen})
      |> skel_map (fun sk -> ExL sk)
  | Atom (NEG, _, _)
  | And (NEG, _, _)
  | True NEG
  | Implies _
  | Forall _
  | Shift _ ->
      Debug.bugf "Rule_gen.active_left_one: negative: @[%a@]" (format_form ()) la

and right_init p pargs =
  [{prems = [] ;
    concl = mk_sequent ()
        ~left:(Ft.singleton (p, pargs))
        ~skel:InitR ;
    eigen = S.empty ;
    extra = M.empty ; sats = [] }]

and left_init p pargs =
  [{prems = [] ;
    concl = mk_sequent ()
        ~right:(p, pargs)
        ~skel:InitL ;
    eigen = S.empty ;
    extra = M.empty ; sats = [] }]

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
              eigen = S.union left_rule.eigen right_rule.eigen ;
              extra = M.merge
                  (fun _ ts1 ts2 -> Some (Option.default [] ts1 @ Option.default [] ts2
                                          (* |> List.sort_unique Pervasives.compare *)))
                  left_rule.extra
                  right_rule.extra ;
              sats = left_rule.sats @ right_rule.sats }
        end right_rules
    end left_rules in
  List.concat rules

let vars_rule rr =
  (* let repls_prems = List.map Sequent.freshen_ rr.prems |> List.map fst in *)
  let repl_concl = Sequent.freshen_ rr.concl |> fst in
  let vs = M.fold (fun v _ vs -> S.add v vs) repl_concl S.empty in
  (* let vs = List.fold_left begin fun vs repl_prem -> *)
  (*     M.fold (fun v _ vs -> S.add v vs) repl_prem vs *)
  (*   end vs repls_prems in *)
  List.map var (S.elements vs)

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
  let (_, f0) = Term.freshen ~repl:M.empty (app lf.label lf.args) in
  match f0.term with
  | App (_, args) ->
      {lf with args = args}
  | _ ->
      Debug.bugf "Rule_gen.freshen_atom: not an app: @[%a@]"
        (format_term ()) f0

let generate0 left pseudo right =
  if List.exists (fun (_, l) -> polarity l <> NEG) left then
    Debug.bugf "generate0: non-negative left" ;
  if List.exists (fun (_, l) -> polarity l <> NEG) pseudo then
    Debug.bugf "generate0: non-negative pseudo" ;
  if polarity right <> POS then
    Debug.bugf "generate0: non-positive right" ;
  let lforms = ref [] in
  let process place hyps =
    List.iter begin
      fun (top, f) ->
        let top = match place with
          | Right -> None
          | _ -> Some top
        in
        let lfs = relabel ~place ?top f in
        lforms := lfs @ !lforms
    end hyps in
  process (Left Global) left ;
  process (Left Pseudo) pseudo ;
  process Right [intern "_", right] ;
  let goal_lform = List.hd !lforms in
  dprintf "label"
    "@[<v0>Labeled formulas:@,  %t@,Goal is %s@]@."
    (fun ff ->
       format_lform ff (List.hd !lforms) ;
       List.iter (Format.fprintf ff "@,  @[%a@]" format_lform) (List.tl !lforms))
    goal_lform.label.rep ;
  (!lforms, goal_lform, generate_rules !lforms)

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
