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
open Seqproof
open Reconstruct

type state = {
  uses : int IdtMap.t ;
}

module Counter : AGENCY with type cert = state =
struct
  type cert = state

  let format_cert ff c =
    let open Format in
    pp_open_box ff 1 ; begin
      pp_print_string ff "{" ; begin
        match IdtMap.bindings c.uses with
        | [] -> ()
        | (x, n) :: us ->
            fprintf ff "%s:%d" x.rep n ;
            List.iter begin fun (x, n) ->
              fprintf ff ",@ %s:%d" x.rep n
            end us ;
      end ;
      pp_print_string ff "}" ;
    end ; pp_close_box ff ()

  let ex_InitR sq _ =
    Choices (List.map fst sq.left_passive)

  let ex_InitL sq _ =
    Choices []

  let cl_TensL sq c =
    match sq.left_active with
    | (x, {form = And (POS, _, _) ; _}) :: _ ->
        Choices [fun xl xr -> c]
    | _ -> Invalid "TensL"

  let ex_TensR sq c =
    match sq.right.form with
    | And (POS, _, _) ->
        Choices [(c, c)]
    | _ -> Invalid "TensR"

  let cl_OneL sq c =
    match sq.left_active with
    | (x, {form = True POS ; _}) :: _ ->
        Choices [c]
    | _ -> Invalid "OneL"

  let ex_OneR sq c =
    match sq.right.form with
    | True POS ->
        Choices []
    | _ -> Invalid "OneR"

  let cl_PlusL sq c =
    match sq.left_active with
    | (x, {form = Or _ ; _}) :: _ ->
        Choices [(fun xx -> c), (fun xx -> c)]
    | _ -> Invalid "PlusL"

  let ex_PlusR sq c =
    match sq.right.form with
    | Or _ ->
        Choices [(`left, c) ; (`right, c)]
    | _ -> Invalid "PlusR"

  let cl_ZeroL sq c =
    match sq.left_active with
    | (x, {form = False ; _}) :: _ ->
        Choices []
    | _ -> Invalid "ZeroL"

  let ex_WithL sq c =
    match sq.left_active with
    | (x, {form = And (NEG, _, _) ; _}) :: _ ->
        Choices [(`left, (fun xx -> c)) ; (`right, (fun xx -> c))]
    | _ -> Invalid "WithL"

  let cl_WithR sq c =
    match sq.right.form with
    | And (NEG, _, _) ->
        Choices [(c, c)]
    | _ -> Invalid "WithR"

  let cl_TopR sq c =
    match sq.right.form with
    | True NEG ->
        Choices []
    | _ -> Invalid "TopR"

  let ex_ImpL sq c =
    match sq.left_active with
    | (x, {form = Implies _ ; _}) :: _ ->
        Choices [(c, (fun xx -> c))]
    | _ -> Invalid "ImpL"

  let cl_ImpR sq c =
    match sq.right.form with
    | Implies _ ->
        Choices [(fun xx -> c)]
    | _ -> Invalid "ImpR"

  let ex_AllL sq c =
    match sq.left_active with
    | (x, {form = Forall _ ; _}) :: _ ->
        let t = Term.vargen#next `evar in
        Choices [(t, (fun xx -> c))]
    | _ -> Invalid "AllL"

  let cl_AllR sq c =
    match sq.right.form with
    | Forall _ -> Choices [fun u -> c]
    | _ -> Invalid "AllR"

  let cl_ExL sq c =
    match sq.left_active with
    | (x, {form = Exists _ ; _}) :: _ ->
        Choices [fun u xx -> c]
    | _ -> Invalid "ExL"

  let ex_ExR sq c =
    match sq.right.form with
    | Exists _ ->
        let t = Term.vargen#next `evar in
        Choices [(t, c)]
    | _ -> Invalid "ExR"

  let ex_BlurR sq c =
    match sq.right.form with
    | Shift _ -> Choices [c]
    | _ -> Invalid "BlurR"

  let ex_BlurL sq c =
    match sq.left_active with
    | [(x, {form = Shift _ ; _})] ->
        Choices [c]
    | _ -> Invalid "BlurL"

  let cl_Store sq c =
    match sq.left_active with
    | _ :: _ ->
        Choices [fun xx -> c]
    | _ -> Invalid "Store"

  let usable left_passive us =
    List.fold_left begin fun cs (x, (_, f)) ->
      if polarity f = POS then cs else
      match IdtMap.find x us.uses with
      (* | 1 -> *)
      (*     let us = {uses = IdtMap.add x 2 us.uses} in *)
      (*     `left (x, fun _ -> us) :: cs *)
      | _ -> cs
      | exception Not_found ->
          (* us.uses <- IdtMap.add x 1 us.uses ; *)
          let us = {uses = IdtMap.add x 1 us.uses} in
          `left (x, fun _ -> us) :: cs
    end [] left_passive

  let ex_Foc sq c =
    match sq.left_active, polarity sq.right, sq.right.form with
    | [], POS, _
    | [], _, Atom (NEG, _, _) ->
        let cs = usable sq.left_passive c in
        let cs = if polarity sq.right = POS then `right c :: cs else cs in
        Choices cs
    | _ -> Invalid "Foc"

end

module Test = struct

  let x = atom NEG (intern "X") []
  let y = atom NEG (intern "Y") []
  let z = atom NEG (intern "Z") []

  let exmon = implies [disj [x ; z] ; implies [x] (disj [y ; z])] (disj [y ; z])
  let counter = implies [x ; implies [x] (conj ~pol:POS [])] x
  let nat = implies [x ; implies [x] x] x


  let (@->) x y = implies [x] y
  let (&&&) x y = conj ~pol:NEG [x ; y]

  let negprod = (x @-> y @-> z) @-> (x &&& y) @-> z
  let negprod2 = ((x @-> y) &&& x) @-> y

  let test = force POS negprod2

  let lforms = relabel test
  (* let lforms = [{place = Right ; *)
  (*                label = intern "foo" ; *)
  (*                args = [] ; *)
  (*                skel = test}] *)

  let goal_lf = List.hd lforms

  let goal = {
    term_vars = IdtMap.empty ;
    left_passive = [] ;
    left_active = [] ;
    right = goal_lf.skel ;
  }

  let cert = {uses = IdtMap.empty}

  let doit () =
    let open Format in
    let open Config in
    let disch = Config.set_proof_channel "/tmp/foo.html" in begin
      pprintf "<pre>--------------------@. %a</pre>@." (format_form ()) goal.right ;
      pprintf "<p>Labeling</p>@.<pre>@." ;
      List.iter (pprintf "%a.@." format_lform) lforms ;
      pprintf "</pre><p>Goal: <code>%s</code></p>@." goal_lf.label.rep ;
      match Reconstruct.reconstruct ~max:10 (module Counter) ~lforms ~goal ~cert with
      | Some pfs ->
          Config.pprintf "<p>Found %d proof(s)</p>@." (List.length pfs) ;
          List.iter (fun pf -> Seqproof_print.print pf ~lforms:lforms ~goal) pfs
      | None ->
          Config.pprintf "<p>No proof found</p>@."
    end ;
    disch ()

end
