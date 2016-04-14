(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014,2015  Inria
 *    (Institut National de Recherche en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Idt
open Term

type polarity = POS | NEG
let dual_polarity = function POS -> NEG | NEG -> POS

type form = {
  form : form_ ;
  vars : VSet.t ;
  (** invariant: fvs(f) \subseteq f.vars   *)
  imax : int ;
  (** invariant: max(-1::fbs(f)) <= f.imax *)
}
and form_ =
  | Atom    of polarity * idt * term list
  | And     of polarity * form * form
  | True    of polarity
  | Or      of form * form
  | False
  | Implies of form * form
  | Exists  of idt * form
  | Forall  of idt * form
  | Shift   of form

let polarity_map : polarity IdtMap.t ref = ref IdtMap.empty
let register_polarity idt pol =
  polarity_map := IdtMap.add idt pol !polarity_map ;
  Format.printf "Predicate %S is now treated as: %s.@." idt.rep
    (match pol with POS -> "POSITIVE" | _ -> "NEGATIVE")

let default_polarity = NEG
let lookup_polarity idt =
  match IdtMap.find_opt idt !polarity_map with
  | Some pol -> pol
  | None ->
      Format.eprintf "No polarity known for %S!@." idt.rep ;
      register_polarity idt default_polarity ;
      default_polarity

let rec polarity f =
  match f.form with
  | Shift f -> dual_polarity @@ polarity f
  | Atom (p, _, _)
  | And (p, _, _)
  | True p -> p
  | Or _ | False | Exists _ -> POS
  | Implies _ | Forall _ -> NEG

let force pol f =
  if polarity f = pol then f else
  match f.form with
  | Shift f -> f
  | _ -> { f with form = Shift f }

let shift f = { f with form = Shift f }
let atom pol pred ts = {
  form = Atom (pol, pred, ts) ;
  imax = List.fold_left Term.(fun mx t -> max mx t.imax) (-1) ts ;
  vars = List.fold_left Term.(fun vs t -> VSet.union vs t.vars) VSet.empty ts ;
}

let conj ?(pol=POS) fs =
  match fs with
  | [] -> { form = True pol ; imax = -1 ; vars = VSet.empty }
  | f :: fs ->
      List.fold_left begin fun g f ->
        let f = force pol f in
        { form = And (pol, g, f) ;
          imax = max g.imax f.imax ;
          vars = VSet.union g.vars f.vars }
      end (force pol f) fs

let disj fs =
  match fs with
  | [] -> { form = False ; imax = -1 ; vars = VSet.empty }
  | f :: fs ->
      List.fold_left begin fun g f ->
        let f = force POS f in
        { form = Or (g, f) ;
          imax = max g.imax f.imax ;
          vars = VSet.union g.vars f.vars }
      end (force POS f) fs

let rec implies fs g =
  match fs with
  | [] -> force NEG g
  | f :: fs ->
      let f = force POS f in
      let g = implies fs g in
      { form = Implies (f, g) ;
        vars = VSet.union f.vars g.vars ;
        imax = max f.imax g.imax }

let forall x f =
  let f = force NEG f in
  { form = Forall (x, f) ;
    imax = max (-1) (f.imax - 1) ;
    vars = f.vars }

let exists x f =
  let f = force POS f in
  { form = Exists (x, f) ;
    imax = max (-1) (f.imax - 1) ;
    vars = f.vars }

let rec app_form ss f0 =
  if f0.imax < 0 then f0 else
  match f0.form with
  | Shift f              -> shift @@ app_form ss f
  | Atom (pol, pred, ts) -> atom pol pred @@ List.map (app_term ss) ts
  | And (pol, pf1, pf2)  -> conj ~pol [app_form ss pf1 ; app_form ss pf2]
  | Or (pf1, pf2)        -> disj [app_form ss pf1 ; app_form ss pf2]
  | ( True _ | False )   -> f0
  | Exists (x, pf)       -> exists x @@ app_form (bump ss 1) pf
  | Implies (pf, nf)     -> implies [app_form ss pf] (app_form ss nf)
  | Forall (x, nf)       -> forall x @@ app_form (bump ss 1) nf

let abstract v f =
  let rec spin depth f =
    match f.form with
    | Shift f -> shift @@ spin depth f
    | Atom (pol, pred, ts) ->
        atom pol pred @@ List.map (spin_term depth) ts
    | And (pol, f1, f2) -> conj ~pol [spin depth f1 ; spin depth f2]
    | Or (f1, f2) -> disj [spin depth f1 ; spin depth f2]
    | (True _ | False) -> f
    | Exists (x, f) -> exists x @@ spin (depth + 1) f
    | Forall (x, f) -> forall x @@ spin (depth + 1) f
    | Implies (f, g) -> implies [spin depth f] (spin depth g)
  and spin_term depth t =
    match t.term with
    | Var _ -> t
    | Idx n when n < depth -> t
    | Idx n -> idx @@ n + 1
    | App (u, []) when u == v -> idx depth
    | App (f, ts) -> app f @@ List.map (spin_term depth) ts
  in
  spin 0 f

let rec replace ?(depth=0) ~repl f0 =
  if VSet.for_all (fun v -> not @@ VMap.mem v repl) f0.vars then f0
  else match f0.form with
    | Shift f              -> shift @@ replace ~depth ~repl f
    | Atom (pol, pred, ts) -> atom pol pred @@ List.map (Term.replace ~depth ~repl) ts
    | And (pol, pf1, pf2)  -> conj ~pol [replace ~depth ~repl pf1 ; replace ~depth ~repl pf2]
    | Or (pf1, pf2)        -> disj [replace ~depth ~repl pf1 ; replace ~depth ~repl pf2]
    | (True _ | False)     -> f0
    | Implies (pf, nf)     -> implies [replace ~depth ~repl pf] @@ replace ~depth ~repl nf
    | Exists (x, pf)       -> exists x @@ replace ~depth:(depth + 1) ~repl pf
    | Forall (x, nf)       -> forall x @@ replace ~depth:(depth + 1) ~repl nf

let __iff_prec     = 050
let __quant_prec   = 100
let __implies_prec = 200
let __or_prec      = 300
let __neg_and_prec = 400
let __pos_and_prec = 500
let __shift_prec   = 600
let __not_prec     = 700
let rec pretty_form ?(cx=[]) ?max_depth f0 =
  let ellipse = match max_depth with
    | None -> false
    | Some d -> d <= 0 in
  if ellipse then Pretty.(Atom (STR "_")) else
  let max_depth = match max_depth with
    | None -> None
    | Some d -> Some (d - 1) in
  match f0.form with
  | Shift f when !Config.show_shifts ->
      let fe = pretty_form ~cx ?max_depth f in
      let op = match polarity f with
        | NEG -> Pretty.FMT "↓"
        | POS -> Pretty.FMT "↑"
      in
      Pretty.(Opapp (__shift_prec, Prefix (op, fe)))
  | Shift f -> pretty_form ~cx ?max_depth f
  | Atom (pol, pred, args) ->
      let pred =
        if !Config.hide_bias then pred else
        intern begin
          match pol with
          | POS -> pred.rep ^ "⁺"
          | NEG -> pred.rep ^ "⁻"
        end
      in
      let pe fmt = format_term ~cx ?max_depth () fmt (app pred args) in
      Pretty.(Atom (FUN pe))
  | And (POS, f1, f2) ->
      let f1e = pretty_form ~cx ?max_depth f1 in
      let f2e = pretty_form ~cx ?max_depth f2 in
      Pretty.(Opapp (__pos_and_prec, Infix (LEFT, f1e, FMT " ⊗@ ", f2e)))
  | And (NEG,
         {form = Implies ({form = Shift a1 ; _}, b1) ; _},
         {form = Implies ({form = Shift b2 ; _}, a2) ; _})
      when a1 = a2 && b1 = b2 ->
      let ae = pretty_form ~cx ?max_depth a1 in
      let be = pretty_form ~cx ?max_depth b1 in
      Pretty.(Opapp (__neg_and_prec, Infix (NON, ae, FMT " ≡@ ", be)))
  | And (NEG, f1, f2) ->
      let f1e = pretty_form ~cx ?max_depth f1 in
      let f2e = pretty_form ~cx ?max_depth f2 in
      Pretty.(Opapp (__neg_and_prec, Infix (LEFT, f1e, FMT " ∧@ ", f2e)))
  | Or (f1, f2) ->
      let f1e = pretty_form ~cx ?max_depth f1 in
      let f2e = pretty_form ~cx ?max_depth f2 in
      Pretty.(Opapp (__or_prec, Infix (LEFT, f1e, FMT " ∨@ ", f2e)))
  | Implies (f1, {form = Shift {form = False ; _} ; _}) ->
      let f1e = pretty_form ~cx ?max_depth f1 in
      Pretty.(Opapp (__not_prec, Prefix (FMT "¬", f1e)))
  | Implies (f1, f2) ->
      let f1e = pretty_form ~cx ?max_depth f1 in
      let f2e = pretty_form ~cx ?max_depth f2 in
      Pretty.(Opapp (__implies_prec, Infix (RIGHT, f1e, FMT " ⊃@ ", f2e)))
  | True POS ->
      Pretty.(Atom (STR "1"))
  | True NEG ->
      Pretty.(Atom (STR "⊤"))
  | False ->
      Pretty.(Atom (STR "⊥"))
  | Forall (x, f) ->
      let fe = pretty_form ~cx:(x :: cx) ?max_depth f in
      let op fmt = Format.fprintf fmt "∀%s.@ " x.rep in
      Pretty.(Opapp (__quant_prec, Prefix (FUN op, fe)))
  | Exists (x, f) ->
      let fe = pretty_form ~cx:(x :: cx) ?max_depth f in
      let op fmt = Format.fprintf fmt "∃%s.@ " x.rep in
      Pretty.(Opapp (__quant_prec, Prefix (FUN op, fe)))

let format_form ?cx ?max_depth () fmt f =
  Pretty.print fmt @@ pretty_form ?cx ?max_depth f

let form_to_string ?(cx=[]) ?max_depth f =
  let buf = Buffer.create 19 in
  let fmt = Format.formatter_of_buffer buf in
  format_form ~cx ?max_depth () fmt f ;
  Format.pp_print_flush fmt () ;
  Buffer.contents buf

let dummygen = new Namegen.namegen
  (fun n -> intern @@ "'" ^ string_of_int n)

let binder mk x f =
  let dummy = dummygen#next in
  let f = f (app dummy []) |>
          force NEG |>
          abstract dummy in
  mk (intern x) f
let forall_ = binder forall
let exists_ = binder exists

type place = Left of left | Right
and left = Global | Pseudo | Local
let change = function Left _ -> Right | Right -> Left Local

let labelgen = new Namegen.namegen1
  (fun n cookie -> intern @@ cookie ^ string_of_int n)

type lform = {
  place : place ;
  label : idt ;
  args  : term list ;
  skel  : form ;
}

let format_lform fmt lf =
  let open Format in
  pp_open_box fmt 2 ; begin
    pp_print_string fmt begin match lf.place with
      | Left lf -> begin
          match lf with
          | Global -> "global "
          | Local -> "local "
          | Pseudo -> "pseudo "
        end
      | Right -> "right "
    end ;
    format_form () fmt @@ atom (polarity lf.skel) lf.label lf.args ;
    pp_print_string fmt " :=" ;
    pp_print_space fmt () ;
    pp_open_box fmt 2 ; begin
      format_form () fmt lf.skel ;
    end ; pp_close_box fmt () ;
  end ; pp_close_box fmt ()

let unvar t = match t.term with
  | Var v -> v
  | _ -> Debug.bugf "unvar on a non-term"

let is_frontier place pol =
  match place, pol with
  | Right, POS
  | Left _, NEG -> true
  | _ -> false

let place_term place args =
  match place with
  | Left _ -> Term.(app (intern "left") args)
  | Right -> Term.(app (intern "right") args)

let pseudo_cookie = "@"
let is_pseudo l = l.rep.[0] = pseudo_cookie.[0]

let place_cookie = function
  | Left Pseudo -> pseudo_cookie
  | _ -> "#"

let relabel ?(place=Right) ~lforms ?top f =
  let lforms = ref lforms in
  let emit_lform lf =
    (* Format.(fprintf std_formatter "  emitted %a@." format_lform lf) ; *)
    lforms := IdtMap.add lf.label lf !lforms
  in
  let memo = Hashtbl.create 19 in
  let rec spin place args f0 =
    match Hashtbl.find memo (place, args, f0) with
    | f -> f
    | exception Not_found -> begin
        let f =
          match f0.form with
          | Shift f when is_frontier place (polarity f) ->
              (* Format.(fprintf std_formatter "  is a frontier@.") ; *)
              let lab = labelgen#next (place_cookie place) in
              (* Format.(fprintf std_formatter "  labelled %s@." lab.rep) ; *)
              let f = spin place args f in
              let args = List.filter begin
                  fun arg -> VSet.mem (unvar arg) f0.vars
                end args in
              emit_lform { place ; label = lab ; args ; skel = f } ;
              shift @@ atom (polarity f) lab args
          | Shift f ->
              (* Format.(fprintf std_formatter "  is NOT a frontier@.") ; *)
              let res = shift @@ spin place args f in
              (* Format.(fprintf std_formatter "  is therefore %a@." (format_form ()) res) ; *)
              res
          | Atom (_, pred, args) -> f0
          | And (pol, pf1, pf2)  ->
              conj ~pol [spin place args pf1 ; spin place args pf2]
          | Or (pf1, pf2)    ->
              disj [spin place args pf1 ; spin place args pf2]
          | (True _ | False) -> f0
          | Exists (x, pf) -> begin
              let v = vargen#next (match place with Right -> E | Left _ -> U) in
              let pf = app_form (Cons (Shift 0, v)) pf in
              let pf = spin place (v :: args) pf in
              let pf = app_form (Shift 1) pf in
              let pf = replace ~depth:0 ~repl:(VMap.digest [unvar v, idx 0]) pf in
              exists x pf
            end
          | Implies (pf, nf) ->
              implies [spin (change place) args pf] @@ spin place args nf
          | Forall (x, nf) -> begin
              let v = vargen#next (match place with Left _ -> E | Right -> U) in
              let nf = app_form (Cons (Shift 0, v)) nf in
              let nf = spin place (v :: args) nf in
              let nf = app_form (Shift 1) nf in
              let nf = replace ~depth:0 ~repl:(VMap.digest [unvar v, idx 0]) nf in
              forall x nf
            end
        in
        Hashtbl.replace memo (place, args, f0) f ;
        f
      end
  in
  let l0 = match top with
    | Some l -> intern (place_cookie place ^ l.rep)
    | None -> labelgen#next (place_cookie place)
  in
  let f0 = match place, polarity f with
    | Left _, POS
    | Right, NEG -> shift f
    | _ -> f
  in
  let weaker_place = function
    | Left _ -> Left Local
    | Right -> Right
  in
  emit_lform { place ; label = l0 ; args = [] ; skel = spin (weaker_place place) [] f0 } ;
  (l0, !lforms)

let expand_fully ~lforms f0 =
  let rec spin f =
    match f.form with
    | Atom (pol, p, ts) -> begin
        match IdtMap.find p lforms with
        | lf ->
            let repl = List.fold_left2 begin
                fun repl lfarg arg ->
                  VMap.add (unvar lfarg) arg repl
              end VMap.empty lf.args ts
            in
            replace ~repl lf.skel |> spin
        | exception Not_found -> f
      end
    | And (pol, f1, f2) -> conj ~pol [spin f1 ; spin f2]
    | Or (f1, f2) -> disj [spin f1 ; spin f2]
    | True _ | False -> f
    | Implies (f1, f2) -> implies [spin f1] (spin f2)
    | Exists (x, f) -> exists x (spin f)
    | Forall (x, f) -> forall x (spin f)
    | Shift f -> shift (spin f)
  in
  spin f0

let rec lp_format ?(cx=[]) () ff f =
  let open Format in
  match f.form with
  | Atom (_, p, ts) ->
      Term.format_term ~cx () ff (app p ts)
  | And (POS, f, g) ->
      fprintf ff "andplus(%a,%a)"
        (lp_format ~cx ()) f
        (lp_format ~cx ()) g
  | And (NEG, f, g) ->
      fprintf ff "andminus(%a,%a)"
        (lp_format ~cx ()) f
        (lp_format ~cx ()) g
  | Or (f, g) ->
      fprintf ff "or(%a,%a)"
        (lp_format ~cx ()) f
        (lp_format ~cx ()) g
  | Implies (f, g) ->
      fprintf ff "implies(%a,%a)"
        (lp_format ~cx ()) f
        (lp_format ~cx ()) g
  | True POS ->
      fprintf ff "trueplus"
  | True NEG ->
      fprintf ff "trueminus"
  | False ->
      fprintf ff "false"
  | Forall (x, f) ->
      fprintf ff "forall(%s\\ %a)" x.rep
        (lp_format ~cx:(x :: cx) ()) f
  | Exists (x, f) ->
      fprintf ff "exists(%s\\ %a)" x.rep
        (lp_format ~cx:(x :: cx) ()) f
  | Shift f ->
      fprintf ff "delay(%a)"
        (lp_format ~cx ()) f

let lp_lform fmt lf =
  let open Format in
  pp_open_box fmt 0 ; begin
    pp_print_string fmt begin match lf.place with
      | Left lf -> begin
          match lf with
          | Global | Local -> "left("
          | Pseudo -> "pseudoleft("
        end
      | Right -> "right("
    end ;
    lp_format () fmt @@ atom (polarity lf.skel) lf.label lf.args ;
    pp_print_string fmt ") :=" ;
    pp_print_space fmt () ;
    pp_open_box fmt 2 ; begin
      lp_format () fmt lf.skel ;
    end ; pp_close_box fmt () ;
  end ; pp_close_box fmt ()

module Test () = struct
  let (x, y, z) = (intern "x", intern "y", intern "z")
  let a = forall x @@ atom POS (intern "a") [idx 0]
  let b = exists x @@ forall y @@ forall z @@
    atom POS (intern "b") [idx 2 ; idx 1 ; idx 0]
  let c = atom POS (intern "c") []
  let f0 = implies [b] @@ disj [a ; b]
  let f1 = implies [conj ~pol:NEG [c ; c]] @@ disj [c ; c]
  let pp x = atom POS (intern "pp") [x]
  let nn x = atom NEG (intern "nn") [x]

  let test f =
    let open Format in
    fprintf std_formatter "Formatting: @[%a@]@." (format_form ()) f ;
    let (l0, lfs) = relabel ~lforms:IdtMap.empty ~place:Right f in
    IdtMap.iter (fun l f -> fprintf std_formatter "%s: %a@." l.rep format_lform f) lfs ;
    lfs

end
