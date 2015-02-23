(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries
module Ft = FingerTree

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
    sqid : int ;
    left : ctx ;
    right : latm option ;
    vars : IdtSet.t ;
    (** invariant: fvs(sq.left) \cup fvs(sq.right) \subseteq sq.vars *)
    inits : ISet.t
  }
  val mk_sequent : ?inits:ISet.t -> ?right:latm -> ?left:ctx -> unit -> sequent
end = struct
  type sequent = {sqid : int ; left : ctx ; right : latm option ;
                  vars : IdtSet.t ; inits : ISet.t}

  let next_sqid =
    let __last = ref 0 in
    fun () -> incr __last ; !__last

  let mk_sequent ?(inits=ISet.empty) ?right ?(left=Ft.empty) () =
    let sqid = next_sqid () in
    let terms = match right with
      | None -> left
      | Some right -> Ft.snoc left right
    in
    let vars = Ft.fold_left begin
        fun vars (_, ts) ->
          List.fold_left begin
            fun vars t -> IdtSet.union vars t.Term.vars
          end vars ts
      end IdtSet.empty terms in
    { sqid ; left ; right ; vars ; inits}
end

include Sq

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

let freshen ?(repl=IdtMap.empty) s0 =
  let (repl, right) = freshen_latm_option ~repl s0.right in
  let (repl, left) = Ft.fold_left begin
      fun (repl, left) elem ->
        let (repl, elem) = freshen_latm ~repl elem in
        (repl, Ft.snoc left elem)
    end (repl, Ft.empty) s0.left in
  mk_sequent ~left ?right ~inits:s0.inits

let subsume_one ~repl (p, pargs) cx =
  let rec spin repls cx =
    match Ft.front cx with
    | Some (cx, (q, qargs)) -> begin
        let repls =
          try fst (Unify.unite_lists ~sym:false repl pargs qargs) :: repls
          with Unify.Unif _ -> repls
        in
        spin repls cx
      end
    | None -> repls
  in
  if Form.is_pseudo p then [repl]
  else spin [] cx

let subsume_all_exn ~repl scx tcx =
  let rec gen repl scx =
    match Ft.front scx with
    | Some (scx, l) ->
        let repls = subsume_one ~repl l tcx in
        test repls scx
    | None -> repl
  and test repls scx =
    match repls with
    | [] -> Unify.unif_fail "all"
    | repl :: repls -> begin
        try gen repl scx
        with Unify.Unif _ -> test repls scx
      end
  in
  gen repl scx

let subsume_full_exn ss0 tt0 =
  let repl = IdtMap.empty in
  let repl =
    match ss0.right, tt0.right with
    | None, rt -> repl
    | Some (p, pargs), Some (q, qargs) when p == q ->
        let (repl, _) = Unify.unite_lists ~sym:false repl pargs qargs in
        repl
    | _ -> Unify.unif_fail "right"
  in
  subsume_all_exn ~repl ss0.left tt0.left

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
  try ignore (subsume_exn ss0 tt0) ; true
  with Unify.Unif _ -> false

let replace_latm ~repl (p, args) =
  (p, List.map (Term.replace ~repl) args)

let replace_sequent ~repl sq =
  let left = Ft.map (replace_latm ~repl) sq.left in
  let right = Option.map (replace_latm ~repl) sq.right in
  mk_sequent ~left ?right ~inits:sq.inits ()

let factor_one ~sc sq =
  let rec gen left right =
    match Ft.front right with
    | None -> ()
    | Some (right, ((p, pargs) as l)) ->
        test left p pargs Ft.empty right ;
        gen (Ft.snoc left l) right
  and test left p pargs middle right =
    match Ft.front right with
    | None -> ()
    | Some (right, ((q, qargs) as m)) ->
        if p == q then begin
          try
            let (repl, pargs) = Unify.unite_lists IdtMap.empty pargs qargs in
            let left = Ft.map (replace_latm ~repl) left in
            let middle = Ft.map (replace_latm ~repl) middle in
            let right = Ft.map (replace_latm ~repl) right in
            let left = Ft.append left @@ Ft.append middle right in
            let left = Ft.snoc left (p, pargs) in
            let right = Option.map (replace_latm ~repl) sq.right in
            sc @@ mk_sequent ~left ?right ~inits:sq.inits ()
          with
          Unify.Unif _ -> ()
        end ;
        test left p pargs (Ft.snoc middle m) right
  in
  gen Ft.empty sq.left

let rec factor ~sc sq =
  let dones = ref [] in
  let worklist = ref [sq] in
  while !worklist <> [] do
    let sq = List.hd !worklist in
    worklist := List.tl !worklist ;
    dones := sq :: !dones ;
    factor_one ~sc:(fun sq -> worklist := sq :: !worklist) sq ;
  done ;
  List.iter sc !dones

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
    end ; pp_close_box fmt () ;
  end ; pp_close_box fmt ()

let sequent_to_string ?max_depth sq =
  let buf = Buffer.create 19 in
  let fmt = Format.formatter_of_buffer buf in
  format_sequent ?max_depth () fmt sq ;
  Format.pp_print_flush fmt () ;
  Buffer.contents buf

type t = sequent

module Test = struct
  let p = Idt.intern "p"
  let q = Idt.intern "q"
  let z = Idt.intern "z"
  let s = Idt.intern "s"
  let _X = fresh_var `evar
  let _a = fresh_var `param
  let _b = fresh_var `param

  let init0 =
    let left = Ft.of_list [(p, [_X]) ; (p, [_a]); (p, [_b])] in
    let right = Some (q, [_X; _a; _b]) in
    mk_sequent ~left ?right ~inits:ISet.empty

  let print sq =
      Format.(fprintf std_formatter "[%d] %a@." sq.sqid (format_sequent ()) sq)

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
          Format.(fprintf std_formatter "   (subsumed by: %d)@." sq.sqid)
      | None ->
          seen := sq :: !seen
    in
    factor sq ~sc:doit ;
    Format.(fprintf std_formatter "Here's what remains after factoring:@.") ;
    List.iter print (List.rev !seen)

  let test_pseudo () =
    let sq0 = mk_sequent ()
        ~left:(Ft.singleton (intern "@a", [])) ~right:(p, []) in
    print sq0 ;
    let sq1 = mk_sequent () ~left:(Ft.of_list [(q, []) ; (p, [])]) ~right:(p, []) in
    print sq1 ;
    subsume sq0 sq1
end
