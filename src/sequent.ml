(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries
module Ft = FingerTree

open Debug

open Idt
open Term

type latm = idt * term list
type ctx = (latm, int) Ft.fg

let ctx_splits ~sc ctx =
  let rec spin left right =
    match Ft.front right with
    | Some (right, x) ->
        sc x (Ft.append left right) ;
        spin (Ft.snoc left x) right
    | None -> ()
  in
  spin Ft.empty ctx

let to_list : ctx -> (idt * term list) list =
  Ft.to_list

module Sq : sig
  type sequent = private {
    left : ctx ;
    right : latm option ;
    vars : VSet.t ;
    (** invariant: fvs(sq.left) \cup fvs(sq.right) \subseteq sq.vars *)
    skel : Skeleton.t ;
    ancs : ISet.t ;
  }
  val mk_sequent : ?ancs:ISet.t -> ?skel:Skeleton.t -> ?right:latm -> ?left:ctx -> unit -> sequent
  val override : ?ancs:ISet.t -> ?skel:Skeleton.t -> ?right:latm option -> ?left:ctx -> sequent -> sequent
end = struct
  type sequent = {
    left : ctx ;
    right : latm option ;
    vars : VSet.t ;
    skel : Skeleton.t ;
    ancs : ISet.t ;
  }

  let mk_sequent ?(ancs=ISet.empty) ?(skel=Skeleton.Prem (Skeleton.premidgen#next)) ?right ?(left=Ft.empty) () =
    let terms = match right with
      | None -> left
      | Some right -> Ft.snoc left right
    in
    let vars = Ft.fold_left begin
        fun vars (_, ts) ->
          List.fold_left begin
            fun vars t -> VSet.union vars t.Term.vars
          end vars ts
      end VSet.empty terms in
    {left ; right ; vars ; skel ; ancs}

  let override ?ancs ?skel ?right ?left sq =
    mk_sequent ()
      ~left:(Option.default sq.left left)
      ?right:(Option.default sq.right right)
      ~skel:(Option.default sq.skel skel)
      ~ancs:(Option.default sq.ancs ancs)
end

include Sq

let format_sequent ?max_depth () fmt sq =
  let open Format in
  pp_open_box fmt 0 ; begin
    pp_open_hovbox fmt 2 ; begin
      begin match Ft.front sq.left with
      | None ->
          pp_print_as fmt 1 "·"
      | Some (left, (p, ts)) ->
          format_term ?max_depth () fmt (app p ts) ;
          Ft.iter begin
            fun (p, ts) ->
              pp_print_string fmt "," ;
              pp_print_space fmt () ;
              format_term ?max_depth () fmt (app p ts) ;
          end left
      end ;
      pp_print_string fmt " -->" ;
      pp_print_space fmt () ; begin
        match sq.right with
        | Some (p, ts) ->
            format_term ?max_depth () fmt (app p ts)
        | None ->
            pp_print_as fmt 1 "·"
      end ;
      if !Config.print_trail then begin
        pp_print_space fmt () ; begin
          pp_print_string fmt "[" ; begin
            match ISet.elements sq.ancs with
            | [] -> ()
            | first :: rest ->
                pp_open_box fmt 0 ; begin
                  pp_print_int fmt first ;
                  List.iter begin fun x ->
                    pp_print_string fmt "," ;
                    pp_print_space fmt () ;
                    pp_print_int fmt x
                  end rest ;
                end ; pp_close_box fmt ()
          end ;
          pp_print_string fmt "]" ;
        end ;
      end ;
    end ; pp_close_box fmt () ;
    (* fprintf fmt "@ @[<b1>[%a]@]" Skeleton.format_skeleton sq.skel ; *)
  end ; pp_close_box fmt ()

let sequent_to_string ?max_depth sq =
  let buf = Buffer.create 19 in
  let fmt = Format.formatter_of_buffer buf in
  format_sequent ?max_depth () fmt sq ;
  Format.pp_print_flush fmt () ;
  Buffer.contents buf


let freshen_latm ~repl (lab, args) =
  let (repl, args) = List.fold_left begin
      fun (repl, args) arg ->
        let (repl, arg) = Term.freshen ~repl arg in
        (repl, arg :: args)
    end (repl, []) args in
  let args = List.rev args in
  (repl, (lab, args))

let freshen_latm_option ~repl lopt =
  match lopt with
  | None -> (repl, None)
  | Some l ->
      let (repl, l) = freshen_latm ~repl l in
      (repl, Some l)

let freshen_ ?(repl=VMap.empty) s0 =
  let (repl, right) = freshen_latm_option ~repl s0.right in
  let (repl, left) = Ft.fold_left begin
      fun (repl, left) elem ->
        let (repl, elem) = freshen_latm ~repl elem in
        (repl, Ft.snoc left elem)
    end (repl, Ft.empty) s0.left in
  (repl, fun () -> override ~left ~right s0)

let freshen ?repl s0 = snd (freshen_ ?repl s0)

let canonize ?(repl=VMap.empty) sq =
  VSet.fold begin fun v repl ->
    if VMap.mem v repl then repl else
      VMap.insert repl v (canonize_var v @@ 1 + VMap.cardinal repl)
  end sq.vars repl

let replace_latm ~repl (p, args) =
  (p, List.map (Term.replace ~repl) args)

let replace_sequent ~repl sq =
  let left = Ft.map (replace_latm ~repl) sq.left in
  let right = Option.map (replace_latm ~repl) sq.right in
  override sq ~left ~right

let format_canonical ff sq =
  let repl = canonize sq in
  let sq = replace_sequent ~repl sq in
  format_sequent () ff sq

let subsume_one ~frz ~repl (p, pargs) cx =
  let rec spin repls front cx =
    match Ft.front cx with
    | Some (cx, ((q, qargs) as l)) when p == q ->
        let repls =
          match Unify.unite_lists ~frz repl pargs qargs with
          | (repl, _) -> (repl, Ft.append front cx) :: repls
          | exception Unify.Unif _ -> repls
        in
        spin repls (Ft.snoc front l) cx
    | Some (cx, l) ->
        spin repls (Ft.snoc front l) cx
    | None -> repls
  in
  if Form.is_pseudo p then [repl, cx]
  else spin [] Ft.empty cx

let subsume_all_exn ~frz ~repl scx tcx =
  let rec gen repl scx tcx =
    match Ft.front scx with
    | Some (scx, l) ->
        let repls = subsume_one ~frz ~repl l tcx in
        test repls scx
    | None -> repl
  and test repls scx =
    match repls with
    | [] -> Unify.unif_fail "all"
    | (repl, tcx) :: repls -> begin
        try gen repl scx tcx
        with Unify.Unif _ -> test repls scx
      end
  in
  gen repl scx tcx

let freeze_sequent sq =
  let ts = List.map snd (Ft.to_list sq.left) |> List.concat in
  let ts = match sq.right with
    | Some (_, rts) -> rts @ ts
    | _ -> ts
  in
  freeze_terms ts

let subsume_full_exn ss0 tt0 =
  let frz = freeze_sequent tt0 in
  let repl = VMap.empty in
  let repl =
    match ss0.right, tt0.right with
    | None, rt -> repl
    | Some (p, pargs), Some (q, qargs) when p == q ->
        let (repl, _) = Unify.unite_lists ~frz repl pargs qargs in
        repl
    | _ -> Unify.unif_fail "right"
  in
  subsume_all_exn ~frz ~repl ss0.left tt0.left

let subsume_test_right sr0 tr0 =
  match sr0, tr0 with
  | None, _ -> true
  | Some (p, pargs), Some (q, args) -> p == q
  | _ -> false

let subsume_test_left sl0 tl0 =
  let rec test p l =
    match Ft.front l with
    | Some (l, (q, _)) ->
        p == q || test p l
    | None -> false
  and gen l =
    match Ft.front l with
    | None -> true
    | Some (l, (p, _)) ->
        (Form.is_pseudo p || test p tl0)
        && gen l
  in
  gen sl0

let subsume_exn ss0 tt0 =
  if subsume_test_right ss0.right tt0.right &&
     subsume_test_left ss0.left tt0.left
  then subsume_full_exn ss0 tt0
  else Unify.unif_fail "subsume_tests"

let subsume ss0 tt0 =
  Config.maybe_timeout () ;
  let tt0 = freshen tt0 () in
  try
    ignore (subsume_exn ss0 tt0) ;
    dprintf "subsumption"
      "@[<v0>[SUBS]@,++ @[%a@]@,-- @[%a@]@]@."
      format_canonical ss0
      format_canonical tt0 ;
    true
  with Unify.Unif _ -> false

let rec unite_arg_lists ~repl args =
  match args with
  | [] -> (repl, [])
  | [arg] -> (repl, arg)
  | arg1 :: arg2 :: args ->
      let (repl, arg1) = Unify.unite_lists repl arg1 arg2 in
      unite_arg_lists ~repl (arg1 :: args)

let ignore_non_unifiable f x =
  try f x with Unify.Unif _ -> ()

let factor_ ~sc sq =
  let rec facts l =
    match l with
    | [] -> [[]]
    | ((p, pargs) as a) :: l ->
        let lf = facts l in
        List.map (fun xs -> (p, [pargs]) :: xs) lf @
        (List.map (fun xs -> comb a xs) lf |> List.concat)

  and comb ((p, pa) as a) xs =
    match xs with
    | [] -> []
    | ((q, qas) as x) :: xs ->
        (if p == q then [(p, pa :: qas) :: xs] else [])
        @
        (List.map (fun y -> x :: y) (comb a xs))
  in
  let rec process_cand (_, cand) =
    let (left, repl) =
      List.fold_left begin
        fun (cx, repl) (p, pas) ->
          let (repl, pas) = unite_arg_lists ~repl pas in
          (Ft.snoc cx (p, pas), repl)
      end (Ft.empty, VMap.empty) cand in
    let sq = override sq ~left in
    sc @@ replace_sequent ~repl sq
  in
  sq.left |>
  Ft.to_list |>
  facts |>
  List.map (fun l -> (List.length l, l)) |>
  List.sort (fun (n, _) (m, _) -> Pervasives.compare n m) |>
  List.iter (ignore_non_unifiable process_cand)

type t = sequent

module Test () = struct
  let p = Idt.intern "p"
  let q = Idt.intern "q"
  let z = Idt.intern "z"
  let s = Idt.intern "s"
  let _X = vargen#next E
  let _a = vargen#next U
  let _b = vargen#next U

  let init0 =
    let left = Ft.of_list [(p, [_X]) ; (p, [_a]); (p, [_b])] in
    let right = Some (q, [_X; _a; _b]) in
    mk_sequent ~left ?right

  let print sq =
      Format.(fprintf std_formatter "%a [%a]@."
                (format_sequent ()) sq
                Skeleton.format_skeleton sq.skel )

  let test sq =
    let seen = ref [] in
    let doit sq =
      print sq ;
      match
        List.Exceptionless.find begin
          fun oldsq -> subsume oldsq sq
        end !seen
      with
      | Some sq ->
          Format.(fprintf std_formatter "   (subsumed by: @[%a@])@." (format_sequent ()) sq)
      | None ->
          seen := sq :: !seen
    in
    factor_ sq ~sc:doit ;
    Format.(fprintf std_formatter "Here's what remains after factoring:@.") ;
    List.iter print (List.rev !seen)

  let test_pseudo () =
    let sq0 = mk_sequent ()
        ~left:(Ft.singleton (intern "@a", [])) ~right:(p, []) in
    print sq0 ;
    let sq1 = mk_sequent () ~left:(Ft.of_list [(q, []) ; (p, [])]) ~right:(p, []) in
    print sq1 ;
    subsume sq0 sq1

  let test_subsume_0 () =
    let open Format in
    let v52 = uvar 52 in
    let v86 = uvar 86 in
    let v87 = uvar 88 in
    let l1 = intern "#1" in
    let l4 = intern "#4" in
    let l5 = intern "#5" in
    let sq_old = mk_sequent ~left:(Ft.of_list [(l4, [v52]) ; (l1, [v52])]) () in
    printf "sq_old: @[%a@]@." (format_sequent ()) sq_old ;
    let sq_new = mk_sequent ~left:(Ft.of_list [(l5, [v86]) ; (l4, [v86]) ; (l1, [v87])]) () in
    printf "sq_new: @[%a@]@." (format_sequent ()) sq_new ;
    let repl = subsume_exn sq_old sq_new in
    printf "repl: %a@." format_repl repl

  let p = uvar
  let v = evar
  let l n = intern @@ "#" ^ string_of_int n
  let test_subsume () =
    let open Format in
    let sq_old = mk_sequent ~left:(Ft.of_list [(l 1, [p 84]) ; (l 6, [p 84]) ;
                                               (l 1, [p 95]) ; (l 1, [p 95])]) () in
    printf "sq_old: @[%a@]@." (format_sequent ()) sq_old ;
    factor_ ~sc:(printf "sq_new: @[%a@]@." (format_sequent ())) sq_old ;
    ()

end
