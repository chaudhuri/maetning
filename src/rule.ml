(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries

open Idt
open Term
open Sequent

type rule = {
  prems : Sequent.t list ;
  concl : Sequent.t ;
  eigen : IdtSet.t ;
}

let format_rule ?max_depth () fmt rr =
  let open Format in
  let format_eigens fmt =
    match IdtSet.elements rr.eigen with
    | [] -> ()
    | v :: vs ->
        pp_open_box fmt 1 ; begin
          pp_print_string fmt " {" ;
          pp_print_string fmt v.rep ;
          List.iter begin fun v ->
            pp_print_string fmt "," ;
            pp_print_cut fmt () ;
            pp_print_string fmt v.rep
          end vs ;
          pp_print_string fmt "}" ;
        end ; pp_close_box fmt ()
  in
  pp_open_vbox fmt 0 ; begin
    if rr.prems <> [] then begin
      List.iteri begin
        fun k prem ->
          format_sequent ?max_depth () fmt prem ;
          pp_print_cut fmt () ;
      end rr.prems ;
      fprintf fmt "--------------------%t@," format_eigens ;
    end ;
    format_sequent ?max_depth () fmt rr.concl ;
    (* Skeleton.format_skeleton fmt rr.concl.skel ; *)
  end ; pp_close_box fmt ()

let foo ff =
  let open Format in
  let bar ff x = pp_print_string ff x in
  pp_print_string ff "abc == " ;
  pp_open_vbox ff 0 ;
  fprintf ff "%a@," bar "x" ;
  fprintf ff "%a@," bar "y" ;
  fprintf ff "%a@]@." bar "z" ;
  pp_close_box ff ()

let ec_viol eigen concl =
  let rec scan_term t =
    match t.term with
    | Var v ->
        IdtSet.mem v eigen
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

let format_repl fmt repl =
  let open Format in
  pp_open_hvbox fmt 1 ; begin
    pp_print_string fmt "{" ;
    IdtMap.iter begin fun v t ->
      pp_print_string fmt v.rep ;
      pp_print_string fmt ":=" ;
      pp_print_space fmt () ;
      Term.format_term () fmt t ;
      pp_print_string fmt ";" ;
      pp_print_space fmt () ;
    end repl ;
    pp_print_string fmt "}" ;
  end ; pp_close_box fmt ()

let rule_match_exn ~sc prem cand =
  (* let sc repl sq = *)
  (*   Format.(eprintf "Succeeded with %a@." *)
  (*             (Sequent.format_sequent ()) sq) ; *)
  (*   sc repl sq *)
  (* in *)
  let repl = IdtMap.empty in
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
        (repl, None, true)
      end
  in
  (* Format.( *)
  (*   eprintf "rule_match: right matched with %a@." format_repl repl *)
  (* ) ; *)
  let rec gen ~repl ~strict left hyps =
    (* Format.( *)
    (*   eprintf "gen: %s@." (if strict then "strict" else "") ; *)
    (*   eprintf "left:@." ; *)
    (*   Ft.iter begin *)
    (*     fun (p, pargs) -> *)
    (*       eprintf "  %a@." (format_term ()) (app p pargs) *)
    (*   end left ; *)
    (*   eprintf "hyps:@." ; *)
    (*   Ft.iter begin *)
    (*     fun (p, pargs) -> *)
    (*       eprintf "  %a@." (format_term ()) (app p pargs) *)
    (*   end hyps ; *)
    (* ) ; *)
    match Ft.front hyps with
    | Some (hyps, (p, pargs)) ->
        (* weaken *)
        gen ~repl ~strict left hyps ;
        (* non-weaken *)
        test left p pargs ~repl ~strict
          ~cont:(fun ~repl ~strict left -> gen ~repl ~strict left hyps) ;
    | None ->
        let sq = override cand ~left:left ~right:right
                 |> replace_sequent ~repl in
        if strict then sc repl sq
        else ((* Format.(eprintf "non-strict discard: %a@." (format_sequent ()) sq) *))
  and test ~repl ~strict ~cont ?(discard=Ft.empty) left p pargs =
    match Ft.front left with
    | Some (left, ((q, qargs) as l)) ->
        if p == q then begin
          try
            (* Format.( *)
            (*   eprintf "  >>> rule_match: %a =?= %a@.  >>> Under: %a@." *)
            (*     (format_term ()) (app p pargs) *)
            (*     (format_term ()) (app q qargs) *)
            (*     format_repl repl ; *)
            (* ) ; *)
            let (repl, _) = Unify.unite_lists repl pargs qargs in
            (* Format.( *)
            (*   eprintf "rule_match: hyp matched with %a@." format_repl repl *)
            (* ) ; *)
            cont ~repl ~strict:true (Ft.append discard left)
          with Unify.Unif _ -> ()
        end ;
        test ~repl ~strict ~cont ~discard:(Ft.snoc discard l) left p pargs
    | None -> ()
  in
  gen ~repl ~strict cand.left prem.left

let rule_match ~sc prem cand =
  try rule_match_exn ~sc prem cand
  with Unify.Unif _ -> ()

let distribute right sq =
  match right, sq.right with
  | Some right, None ->
      override sq ~right:(Some right)
  | _ -> sq

let specialize_one ~sc ~sq ~concl ~eigen current_prem remaining_prems =
  rule_match current_prem sq ~sc:begin
    fun repl sq ->
      let prems = List.map (replace_sequent ~repl) remaining_prems in
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
      let concl = distribute sq.right concl in
      let old_eigen = eigen in
      let eigen = replace_eigen_set ~repl eigen in
      (* if IdtSet.cardinal old_eigen <> IdtSet.cardinal eigen then *)
      (*   Format.( *)
      (*     eprintf "old_eigen: %s@." (IdtSet.elements old_eigen |> *)
      (*                                List.map (fun x -> x.rep) |> *)
      (*                                String.concat ",") ; *)
      (*     eprintf "eigen: %s@." (IdtSet.elements eigen |> *)
      (*                            List.map (fun x -> x.rep) |> *)
      (*                            String.concat ",") ; *)
      (*   ) ; *)
      if IdtSet.cardinal old_eigen == IdtSet.cardinal eigen &&
         not @@ ec_viol eigen concl
      then
        let prem_vars = List.fold_left begin
            fun vars sq -> IdtSet.union vars sq.vars
          end IdtSet.empty prems in
        let eigen = IdtSet.inter eigen prem_vars in
        let concl = override concl
            ~skel:(Skeleton.reduce [concl.skel ; sq.skel]) in
        sc { prems ; concl ; eigen }
      (* else *)
      (*   Format.( *)
      (*     eprintf "Killed: %a@.with eigen: %s@." *)
      (*       (format_sequent ()) concl *)
      (*       (IdtSet.elements old_eigen |> *)
      (*        List.map (fun x -> x.rep) |> *)
      (*        String.concat ",") *)
      (*   ) *)
  end

let specialize ~sc rr sq =
  let rec spin left right =
    match right with
    | [] -> ()
    | prem :: right ->
        specialize_one prem (List.rev_append left right)
          ~sc ~sq ~concl:rr.concl ~eigen:rr.eigen ;
        spin (prem :: left) right
  in
  spin [] rr.prems

let factor_loop ~sc sq =
  let seen = ref [] in
  let doit sq =
    if List.exists (fun seensq -> Sequent.subsume seensq sq) !seen then begin
      (* Format.(eprintf "factor_loop: killed %a@." *)
      (*           (format_sequent ()) sq) *)
    end else begin
      sc sq ;
      seen := sq :: !seen
    end
  in
  Sequent.factor sq ~sc:doit

let specialize_default ~sc_rule ~sc_fact rr sq =
  let sc rule =
    match rule.prems with
    | [] -> factor_loop ~sc:sc_fact rule.concl
    | _ -> sc_rule rule
  in
  specialize ~sc rr sq

let rule_subsumes_exn r1 r2 =
  let repl = Sequent.subsume_exn r1.concl r2.concl in
  let _repl =
    List.fold_left2 begin
      fun repl p1 p2 ->
        let p1 = Sequent.replace_sequent ~repl p1 in
        let p2 = Sequent.replace_sequent ~repl p2 in
        Sequent.subsume_exn p1 p2
    end repl r1.prems r2.prems
  in
  true

let rule_subsumes r1 r2 =
  List.length r1.prems = List.length r2.prems
  && (try rule_subsumes_exn r1 r2 with Unify.Unif _ -> false)

let rule_subsumes_loudly r1 r2 =
  let res = rule_subsumes r1 r2 in
  if res then
    Format.(
      fprintf std_formatter
        "   >>> @[<v0>@[%a@]@,subsumes@,@[%a@]@] <<<@."
        (format_rule ()) r1
        (format_rule ()) r2
    ) ;
  res

module Test = struct
  let p = Idt.intern "p"
  let q = Idt.intern "q"
  let z = app (Idt.intern "z") []
  let s x = app (Idt.intern "s") [x]
  let _X = fresh_var `evar
  let _Y = fresh_var `evar
  let _a = fresh_var `param
  let _b = fresh_var `param
  let _c = fresh_var `param

  let rule1 = {
    prems = [ mk_sequent ~left:Ft.empty ~right:(p, [_X ; _a]) () ] ;
    concl = mk_sequent ()
        ~left:(Ft.of_list [(q, [_X])])
        ~right:(q, [_X]) ;
    eigen = IdtSet.singleton (unvar _a)
  }

  let sq1 = mk_sequent ()
      ~left:(Ft.of_list [(q, [_Y])])
      ~right:(p, [s z ; _b])

  let rule2 = {
    prems = [ mk_sequent ()
                ~left:(Ft.of_list [(q, [z])]) ;
              mk_sequent ()
                ~left:(Ft.of_list [(q, [s z])]) ] ;
    concl = mk_sequent ()
        ~left:(Ft.singleton (q, [app (Idt.intern "nat") []])) ;
    eigen = IdtSet.empty
  }

  let sq2 = mk_sequent () ~left:(Ft.singleton (q, [_X])) ~right:(q, [s _X])

  let print rr =
    let open Format in
    fprintf std_formatter "rule @[<h>%a@]@." (format_rule ()) rr

  let test rule sq =
    let sc_fact = Sequent.Test.print in
    let sc_rule = print in
    Sequent.Test.print sq ;
    print rule ;
    specialize_default ~sc_rule ~sc_fact rule sq

end
