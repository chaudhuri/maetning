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
open Sequent

module M = IdtMap
module S = IdtSet

type right_mode = [`extract | `test]

type rule = {
  prems : (Sequent.t * right_mode) list ;
  concl : Sequent.t ;
  sats  : Sequent.t list ;
  eigen : VSet.t ;
  extra : term list VMap.t ;
}

let canonize ?(repl=VMap.empty) rr =
  let (repl, prems) = List.fold_left begin
      fun (repl, prems) (prem, mode) ->
        let repl = Sequent.canonize ~repl prem in
        (repl, (Sequent.replace_sequent ~repl prem, mode) :: prems)
    end (repl, []) rr.prems in
  let prems = List.rev prems in
  let repl = Sequent.canonize ~repl rr.concl in
  let concl = Sequent.replace_sequent ~repl rr.concl in
  let (repl, sats) = List.fold_left begin
      fun (repl, sats) sat ->
        let repl = Sequent.canonize ~repl sat in
        (repl, Sequent.replace_sequent ~repl sat :: sats)
    end (repl, []) rr.sats in
  let sats = List.rev sats in
  let eigen = replace_eigen_set ~repl rr.eigen in
  let extra = VMap.fold begin
      fun u ts extra ->
        let v = replace_eigen ~repl u in
        let ts = List.map (Term.replace ~repl) ts in
        VMap.add v ts extra
    end rr.extra VMap.empty
  in
  { prems ; concl ; sats ; eigen ; extra }

let format_eigen ff eigen =
  match VSet.elements eigen with
  | [] -> ()
  | v :: vs ->
      Format.(
        pp_open_box ff 1 ; begin
          pp_print_string ff "{" ;
          format_var ff v ;
          List.iter (fun v -> fprintf ff ",@,%a" format_var v) vs ;
          pp_print_string ff "}" ;
        end ; pp_close_box ff ()
      )

let format_terms ff ts =
  match ts with
  | [] -> ()
  | t :: ts ->
      format_term () ff t ;
      List.iter (Format.fprintf ff ",@,%a" (format_term ())) ts

let format_extra1 ff (x, ts) =
  let open Format in
  List.iter begin fun t ->
    fprintf ff "%a#@[<b1>[%a]@]"
      format_var x format_terms ts
  end ts

let format_extra ff extra =
  let open Format in
  match VMap.bindings extra with
  | [] -> ()
  | xts :: bs ->
      pp_open_box ff 1 ; begin
        pp_print_string ff "{" ;
        format_extra1 ff xts ;
        List.iter (fprintf ff ",@,%a" format_extra1) bs ;
        pp_print_string ff "}" ;
      end ; pp_close_box ff ()

let format_rule ?max_depth () fmt rr =
  let rr = canonize rr in
  let open Format in
  pp_open_vbox fmt 0 ; begin
    if rr.prems <> [] then begin
      List.iteri begin
        fun k (prem, mode) ->
          format_sequent ?max_depth () fmt prem ;
          if mode = `test then pp_print_string fmt "@" ;
          (* fprintf fmt " [%a]" Skeleton.format_skeleton prem.skel ; *)
          pp_print_cut fmt () ;
      end rr.prems ;
      if not !Config.shrink && rr.sats <> [] then begin
        List.iteri begin
          fun k sat ->
            pp_print_string fmt "{" ;
            format_sequent ?max_depth () fmt sat ;
            pp_print_string fmt "}" ;
            pp_print_cut fmt () ;
        end rr.sats ;
      end ;
      fprintf fmt "-------------------- %a %a@," format_eigen rr.eigen format_extra rr.extra ;
    end ;
    format_sequent ?max_depth () fmt rr.concl ;
    (* fprintf fmt " [%a]" Skeleton.format_skeleton rr.concl.skel ; *)
  end ; pp_close_box fmt ()

let ec_viol eigen concl =
  let rec scan_term t =
    match t.term with
    | Var v ->
        VSet.mem v eigen
    | App (_, ts) -> scan_terms ts
    | _ -> false

  and scan_terms ts =
    List.exists scan_term ts

  and scan_one p args =
    if !Config.evc_pseudos || not (Form.is_pseudo p) then
      scan_terms args
    else false

  and scan left =
    match Ft.front left with
    | Some (left, (p, args)) ->
        scan_one p args || scan left
    | None -> begin
        match concl.right with
        | None -> false
        | Some (_, args) ->
            scan_terms args
      end
  in
  scan concl.left

let evc_ok eigen concl =
  let ret = ec_viol eigen concl in
  if ret then
    dprintf "evc"
      "rejecting @[%a@] -- EVS = %s@."
      (format_sequent ()) concl
      (String.concat "," @@ List.map var_to_string (VSet.elements eigen)) ;
  not ret

let rec occurs v t =
  match t.term with
  | Var u -> v = u
  | App (_, ts) -> List.exists (occurs v) ts
  | Idx _ -> false

let extra_ok extra =
  VMap.for_all begin fun v ts ->
    List.for_all begin fun t ->
      not @@ occurs v t
    end ts
  end extra

let rule_match_exn ~sc (prem, mode) cand =
  let repl = VMap.empty in
  let (repl, right, strict) =
    match prem.right, cand.right with
    | None, _ ->
        (repl, cand.right, false)
    | _, None ->
        (repl, None, false)
    | Some (p, pargs), Some (q, qargs) -> begin
        (* Format.(eprintf "p = %s, q = %s@." p.rep q.rep) ; *)
        if p != q then Unify.unif_fail "right hand sides" ;
        (* let (repl, args) = Unify.unite_match_lists repl pargs qargs in *)
        let (repl, args) = Unify.unite_lists repl pargs qargs in
        (repl, None, mode = `extract)
      end
  in
  let rec gen ~repl ~strict cleft pleft =
    match Ft.front pleft with
    | Some (pleft, (p, pargs)) ->
        test ~repl ~strict cleft pleft p pargs
    | None ->
        let sq = override cand ~left:cleft ~right |>
                 replace_sequent ~repl in
        if strict then sc repl sq
        else ()
  and test ~repl ~strict ?(did=false) ?(discard=Ft.empty) cleft pleft p pargs =
    match Ft.front cleft with
    | None ->
        if not did then gen ~repl ~strict discard pleft
    | Some (cleft, ((q, qargs) as l)) ->
        if p == q then begin
          match Unify.unite_lists repl pargs qargs with
          | (repl_succ, _) ->
              gen ~repl:repl_succ ~strict:true (Ft.append discard cleft) pleft ;
              test ~repl ~strict ~did:true ~discard:(Ft.snoc discard l) cleft pleft p pargs
          | exception Unify.Unif _ ->
              test ~repl ~strict ~did ~discard:(Ft.snoc discard l) cleft pleft p pargs
        end else
          test ~repl ~strict ~did ~discard:(Ft.snoc discard l) cleft pleft p pargs
  in
  gen ~repl ~strict cand.left prem.left

let rule_match ~sc prem cand =
  try rule_match_exn ~sc prem cand
  with Unify.Unif _ -> ()

let distribute right (sq, mode) =
  match right, sq.right with
  | Some right, None ->
      (override sq ~right:(Some right), `test)
  | _ ->
      (sq, mode)

let specialize_one ~sc ~id ~sq ~concl ~sats ~eigen ~extra ((current_prem, current_mode) as current) remaining_prems =
  let current_premid = match current_prem.skel with
    | Skeleton.Prem k -> k
    | _ -> failwith "Invalid premise"
  in
  let sq0 = sq in
  rule_match current sq ~sc:begin
    fun repl sq ->
      let sats = List.map (replace_sequent ~repl) (sq0 :: sats) in
      let prems = List.map (fun (sq, mode) -> (replace_sequent ~repl sq, mode)) remaining_prems in
      let new_hyps =
        let removed = Ft.to_list current_prem.left in
        let removed = List.map (replace_latm ~repl) removed in
        Ft.to_list sq.left |>
        List.filter (fun hyp -> not @@ List.mem hyp removed) |>
        Ft.of_list
      in
      let concl = replace_sequent ~repl concl in
      let concl = override concl ~left:(Ft.append concl.left new_hyps) in
      let prems = List.map (distribute sq.right) prems in
      let concl = distribute sq.right (concl, `test) |> fst in
      let extra = VMap.fold begin
          fun v ts extra ->
            let newts = List.map (Term.replace ~repl) ts in
            let v = Term.replace_eigen ~repl v in
            let ts = match VMap.find v extra with
              | oldts -> oldts @ newts
              | exception Not_found -> newts
            in
            VMap.add v ((* List.sort_uniq Pervasives.compare *) ts) extra
        end extra VMap.empty
      in
      let old_eigen = eigen in
      let eigen = replace_eigen_set ~repl eigen in
      (* if S.cardinal old_eigen <> S.cardinal eigen then *)
      (*   Format.( *)
      (*     eprintf "old_eigen: %s@." (S.elements old_eigen |> *)
      (*                                List.map (fun x -> x.rep) |> *)
      (*                                String.concat ",") ; *)
      (*     eprintf "eigen: %s@." (S.elements eigen |> *)
      (*                            List.map (fun x -> x.rep) |> *)
      (*                            String.concat ",") ; *)
      (*   ) ; *)
      if VSet.cardinal old_eigen == VSet.cardinal eigen &&
         evc_ok eigen concl && extra_ok extra
      then
        let prem_vars = List.fold_left begin
            fun vars (sq, _) -> VSet.union vars sq.vars
          end VSet.empty prems in
        let eigen = VSet.inter eigen prem_vars in
        let extra = VMap.filter (fun v _ -> VSet.mem v prem_vars) extra in
        let concl = override concl
            ~ancs:(ISet.add id (ISet.union sq.ancs concl.ancs))
            ~skel:(Skeleton.reduce [(concl.skel, -1) ; (sq.skel, current_premid)]) in
        sc { prems ; concl ; sats ; eigen ; extra }
      (* else *)
      (*   Format.( *)
      (*     eprintf "Killed: %a@.with eigen: %s@." *)
      (*       (format_sequent ()) concl *)
      (*       (S.elements old_eigen |> *)
      (*        List.map (fun x -> x.rep) |> *)
      (*        String.concat ",") *)
      (*   ) *)
  end

let specialize_any ~sc rr (id, sq) =
  let rec spin left right =
    match right with
    | [] -> ()
    | prem :: right ->
        specialize_one prem (List.rev_append left right)
          ~sc ~id ~sq ~concl:rr.concl ~eigen:rr.eigen ~extra:rr.extra ~sats:rr.sats ;
        spin (prem :: left) right
  in
  spin [] rr.prems

let specialize_left ~sc rr (id, sq) =
  match rr.prems with
  | [] -> ()
  | prem :: prems ->
      specialize_one prem prems
        ~sc ~id ~sq ~concl:rr.concl ~eigen:rr.eigen ~extra:rr.extra ~sats:rr.sats

let specialize_default ?(spec=specialize_left) ~sc_rule ~sc_fact rr idsq =
  let sc rule =
    match rule.prems with
    | [] ->
        sc_fact rule.concl
    | _ ->
        sc_rule rule
  in
  spec ~sc rr idsq

let freshen ?(repl=VMap.empty) rr =
  let (repl, concl) = Sequent.freshen_ ~repl rr.concl in
  let concl = concl () in
  let (repl, prems) = List.fold_right begin
      fun (sq, mode) (repl, prems) ->
        let (repl, sq) = Sequent.freshen_ ~repl sq in
        (repl, (sq (), mode) :: prems)
    end rr.prems (repl, [])
  in
  let (repl, sats) = List.fold_right begin
      fun sq (repl, sats) ->
        let (repl, sqf) = Sequent.freshen_ ~repl sq in
        (repl, sqf () :: sats)
    end rr.sats (repl, [])
  in
  let eigen = replace_eigen_set ~repl rr.eigen in
  let extra = VMap.fold begin
      fun u ts extra ->
        let v = replace_eigen ~repl u in
        let ts = List.map (Term.replace ~repl) ts in
        VMap.add v ts extra
    end rr.extra VMap.empty
  in
  { prems ; concl ; sats ; eigen ; extra }

let rule_subsumes_exn r1 r2 =
  let repl = Sequent.subsume_exn r1.concl r2.concl in
  let _repl =
    List.fold_left2 begin
      fun repl (p1, _) (p2, _) ->
        let p1 = Sequent.replace_sequent ~repl p1 in
        let p2 = Sequent.replace_sequent ~repl p2 in
        Sequent.subsume_exn p1 p2
    end repl r1.prems r2.prems
  in
  true

let rule_subsumes r1 r2 =
  !Config.rule_sub
  && List.length r1.prems = List.length r2.prems
  && (try rule_subsumes_exn r1 r2 with Unify.Unif _ -> false)

module Test () = struct
  let p = Idt.intern "p"
  let q = Idt.intern "q"
  let z = app (Idt.intern "z") []
  let s x = app (Idt.intern "s") [x]
  let _X = vargen#next E
  let _Y = vargen#next E
  let _a = vargen#next U
  let _b = vargen#next U
  let _c = vargen#next U

  let rule1 = {
    prems = [ mk_sequent ~left:Ft.empty ~right:(p, [_X ; _a]) (), `extract ] ;
    concl = mk_sequent ()
        ~left:(Ft.of_list [(q, [_X])])
        ~right:(q, [_X]) ;
    eigen = VSet.singleton (unvar _a) ;
    extra = VMap.empty ;
    sats = [] ;
  }

  let sq1 = mk_sequent ()
      ~left:(Ft.of_list [(q, [_Y])])
      ~right:(p, [s z ; _b])

  let rule2 = {
    prems = [ mk_sequent ()
                ~left:(Ft.of_list [(q, [z])]), `extract ;
              mk_sequent ()
                ~left:(Ft.of_list [(q, [s z])]), `extract ] ;
    concl = mk_sequent ()
        ~left:(Ft.singleton (q, [app (Idt.intern "nat") []])) ;
    eigen = VSet.empty ;
    extra = VMap.empty ;
    sats = [] ;
  }

  let sq2 = mk_sequent () ~left:(Ft.singleton (q, [_X])) ~right:(q, [s _X])

  let print rr =
    let open Format in
    fprintf std_formatter "rule @[<h>%a@]@." (format_rule ()) rr

  module STest = Sequent.Test ()

  let test rule sq =
    let sc_fact = STest.print in
    let sc_rule = print in
    STest.print sq ;
    print rule ;
    specialize_default ~sc_rule ~sc_fact rule (0, sq)

end
