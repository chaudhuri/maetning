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

let global_map : Form.form IdtMap.t ref = ref IdtMap.empty
let pseudo_map : Form.form IdtMap.t ref = ref IdtMap.empty

let ensure_new x =
  if IdtMap.mem x !global_map ||
     IdtMap.mem x !pseudo_map ||
     (not !Config.tptp && IdtMap.mem x !polarity_map)
  then begin
    Format.eprintf "Name %S already used..@." x.rep ;
    failwith "ensure_new"
  end

let add_global x f =
  ensure_new x ;
  let f = force NEG f in
  global_map := IdtMap.add x f !global_map ;
  Format.printf "Added global %s : %a.@." x.rep (Form.format_form ()) f ;
  Config.pprintf "<p>Assuming <code>#%s : %a</code>.</p><hr>@."
    x.rep (Form.format_form ()) f

let add_pseudo x f =
  ensure_new x ;
  let f = force NEG f in
  pseudo_map := IdtMap.add x f !pseudo_map ;
  Format.printf "Added pseudo %s : %a.@." x.rep (Form.format_form ()) f ;
  Config.pprintf "<p>Assuming <code>@@%s : %a</code>.</p><hr>@."
    x.rep (Form.format_form ()) f

let retract x =
  let (map, map_name) =
    if IdtMap.mem x !global_map then (global_map, "global")
    else if IdtMap.mem x !pseudo_map then (pseudo_map, "pseudo")
    else failwith ("Unknown assumption or pseudo " ^ x.rep)
  in
  map := IdtMap.remove x !map ;
  Format.printf "Removed %s %s.@." map_name x.rep

let values map =
  IdtMap.fold (fun _ v l -> v :: l) map []

type outcome =
  | Proved of Sequent.t
  | Refuted
  | Unsound of Idt.t * Sequent.t

let dep_salt = new Namegen.namegen (fun n -> n)

let setup f =
  let open Sequent in
  let f = force POS f in
  (* Format.printf "Goal: %a.@." (Form.format_form ()) f ; *)
  (* let globals = values !global_map in *)
  (* let pseudo = values !pseudo_map in *)
  let prover_result =
    let res = Inverse.inverse_method f
        ~left:(IdtMap.bindings !global_map)
        ~pseudo:(IdtMap.bindings !pseudo_map)
    in
    match res.Inverse.status with
    | None -> {res with Inverse.status = Refuted}
    | Some resq -> begin
        match
          Ft.to_list resq.left |>
          List.Exceptionless.find (fun (p, _) -> Form.is_pseudo p)
        with
        | None -> {res with Inverse.status = Proved resq}
        | Some (p, _) -> {res with Inverse.status = Unsound (p, resq)}
      end
  in
  begin match !Config.dump_database with
  | None -> ()
  | Some ff ->
      Format.fprintf ff "---- BEGIN DATABASE ----@." ;
      Inverse.Data.iter_known begin fun sq ->
        Format.fprintf ff "[%d] %a@." sq.Inverse.id Sequent.format_canonical sq.Inverse.th
      end ;
      Format.fprintf ff "---- END DATABASE ----@." ;
  end ;
  begin match !Config.dependency_dag with
  | None ->  ()
  | Some ff ->
      let open Format in
      let known_ids = ref ISet.empty in
      Inverse.Data.iter_known begin fun sq ->
        known_ids := ISet.add sq.Inverse.id !known_ids
      end ;
      let salt = dep_salt#next in
      Inverse.Data.iter_known begin fun sq ->
        fprintf ff "s_%d_%d [shape=box,label=\"[%d] %s\"];@."
          salt sq.Inverse.id
          sq.Inverse.id (Sequent.sequent_to_string sq.Inverse.th) ;
        ISet.iter begin fun anc ->
          if ISet.mem anc !known_ids then
            fprintf ff "s_%d_%d -> s_%d_%d;@." salt anc salt sq.Inverse.id
        end sq.Inverse.th.ancs
      end ;
  end ;
  prover_result

let dump_proof ?(pseudos=false) f res =
  Seqproof.hypgen#reset ;
  let ctx = List.filter_map begin fun (l, lf) ->
      match lf.place with
      | Left Global ->
          Some (lf.Form.label, (lf.Form.label, lf.Form.skel))
      | Left Pseudo when pseudos ->
          Some (lf.Form.label, (lf.Form.label, lf.Form.skel))
      | _ -> None
    end (IdtMap.bindings res.Inverse.lforms) in
  let goal = Seqproof.{term_vars = IdtMap.empty ;
                       left_active = [] ;
                       left_passive = IdtMap.digest ctx ;
                       right = res.Inverse.goal.Form.skel}
  in
  match Reconstruct.reconstruct (module Agencies.Rebuild)
          ~max:1
          ~lforms:res.Inverse.lforms
          ~goal
          ~cert:res.Inverse.status.Sequent.skel
  with
  | Some prf ->
      Config.pprintf "<p>Proof for <code>%a</code></p>@." (Form.format_form ()) f ;
      if pseudos then Config.pprintf "<p class='pseudo'>THIS IS A PSEUDO PROOF</p>@." ;
      Seqproof_print.print prf
        ~lforms:res.Inverse.lforms ~goal ;
      Config.pprintf "<hr>@."
  | None -> failwith "Reconstruction failed"

let dump_model f res =
  match Model.create_model res with
  | Model.Sat ->
      Debug.bugf "Model for %a was satisfying" (Form.format_form ()) f
  | Model.Counter modl ->
      Config.pprintf "<p>Countermodel for <code>%a</code></p>@." (Form.format_form ()) f ;
      if !Config.dot_models then
        Config.pprintf "%s@." (Model.dot_format_model modl)
      else
        Config.pprintf "<pre>@.%a</pre>@." Model.format_model modl ;
      if Model.validate_model res modl then
        (* Debug.dprintf "modelcheck" "!!!!! Reconstructed model is satisfying !!!!!@." ; *)
        Debug.bugf "!!!!! Reconstructed model is satisfying !!!!!@." ;
      Config.pprintf "<hr>@."

let prove f =
  let res = setup f in
  match res.Inverse.status with
  | Proved sq ->
      if !Config.do_check then dump_proof f {res with Inverse.status = sq} ;
      Format.printf "Proved.@."
  | Refuted ->
      if !Config.do_check then dump_model f res ;
      failwith "Not provable"
  | Unsound (p, sq) ->
      if !Config.pseudo_proofs then dump_proof ~pseudos:true f {res with Inverse.status = sq} ;
      Format.printf "UNKNOWN: pseudo %s was used.@." p.rep

let refute f =
  let res = setup f in
  match res.Inverse.status with
  | Proved _ -> failwith "Not refuted"
  | Refuted ->
      if !Config.do_check then dump_model f res ;
      Format.printf "Refuted.@."
  | Unsound (p, sq) ->
      if !Config.pseudo_proofs then dump_proof ~pseudos:true f {res with Inverse.status = sq} ;
      Format.printf "UNKNOWN: pseudo %s was used.@." p.rep
