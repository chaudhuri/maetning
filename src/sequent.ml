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

type latm = idt * term list

module Ctx : sig
  type t = private term list list IdtMap.t

  val empty : t
  val singleton : idt -> term list -> t
  val singleton_latm : latm -> t

  val add : idt -> term list -> t -> t
  val add_latm : latm -> t -> t

  val join : t -> t -> t

  val pop : t -> latm * t

  val replace : repl:term VMap.t -> t -> t

  val map : (idt -> term list -> term list) -> t -> t
  val iter : (idt -> term list -> unit) -> t -> unit

  val fold : (idt -> term list -> 'acc -> 'acc) -> t -> 'acc -> 'acc

  val to_list : t -> latm list

  val pp : Format.formatter -> t -> unit
end = struct
  type t = term list list IdtMap.t

  let empty = IdtMap.empty

  let singleton p ts = IdtMap.singleton p [ts]

  let singleton_latm (p, ts) = singleton p ts

  let to_list ctx =
    IdtMap.bindings ctx
    |> List.map (fun (p, tss) -> List.map (fun ts -> (p, ts)) tss)
    |> List.concat

  let add p ts ctx =
    let tss =
      match IdtMap.find p ctx with
      | tss -> tss
      | exception Not_found -> []
    in
    IdtMap.add p (ts :: tss) ctx

  let add_latm (p, ts) ctx = add p ts ctx

  let join ctx1 ctx2 =
    IdtMap.merge begin fun p tss1 tss2 ->
      let tss1 = Option.default [] tss1 in
      let tss2 = Option.default [] tss2 in
      Some (List.rev_append tss1 tss2)
    end ctx1 ctx2

  let pop ctx =
    let ((p, tss), ctx) = IdtMap.pop ctx in
    match tss with
    | [] -> bugf "Ctx.pop: empty list of spines"
    | [ts] ->
        ((p, ts), ctx)
    | ts :: tss ->
        ((p, ts), IdtMap.add p tss ctx)

  let replace ~repl ctx =
    IdtMap.map begin fun tss ->
      List.map begin fun ts ->
        List.map (Term.replace ~repl) ts
      end tss
    end ctx

  let map fn ctx =
    IdtMap.mapi begin fun p tss ->
      List.map begin fun ts ->
        fn p ts
      end tss
    end ctx

  let iter fn ctx =
    IdtMap.iter begin fun p tss ->
      List.iter begin fun ts ->
        fn p ts
      end tss
    end ctx

  let fold fn ctx acc =
    IdtMap.fold begin fun p tss acc->
      List.fold_left begin fun acc ts ->
        fn p ts acc
      end acc tss
    end ctx acc

  let pp ff ctx =
    let binds =
      to_list ctx |>
      List.map begin
        fun (p, ts) () ->
          format_term () ff (app p ts)
      end |>
      List.interleave begin
        fun () ->
          Format.pp_print_string ff "," ;
          Format.pp_print_space ff ()
      end
    in
    Format.(
      pp_open_box ff 2 ;
      List.iter (fun f -> f ()) binds ;
      pp_close_box ff ()
    )
end

module Sq : sig
  type sequent = private {
    left : Ctx.t ;
    pseudo : Ctx.t ;
    right : latm option ;
    vars : VSet.t ;
    (** invariant: fvs(sq.left) \cup fvs(sq.right) \subseteq sq.vars *)
    skel : Skeleton.t ;
    ancs : ISet.t ;
  }
  val mk_sequent : ?ancs:ISet.t -> ?skel:Skeleton.t -> ?right:latm -> ?left:Ctx.t -> ?pseudo:Ctx.t ->
    unit -> sequent
  val override : ?ancs:ISet.t -> ?skel:Skeleton.t -> ?right:latm option -> ?left:Ctx.t -> ?pseudo:Ctx.t ->
    sequent -> sequent
end = struct
  type sequent = {
    left : Ctx.t ;
    pseudo : Ctx.t ;
    right : latm option ;
    vars : VSet.t ;
    skel : Skeleton.t ;
    ancs : ISet.t ;
  }

  let terms_vars vs ts =
    List.fold_left begin fun vs t ->
      VSet.union vs t.Term.vars
    end vs ts

  let mk_sequent
      ?(ancs=ISet.empty)
      ?(skel=Skeleton.Prem (Skeleton.premidgen#next))
      ?right ?(left=Ctx.empty)
      ?(pseudo=Ctx.empty)
      () =
    let vars = match right with
      | Some (_, ts) -> terms_vars VSet.empty ts
      | None -> VSet.empty
    in
    let vars = Ctx.fold (fun _ ts vs -> terms_vars vs ts) left vars in
    let vars = Ctx.fold (fun _ ts vs -> terms_vars vs ts) pseudo vars in
    {left ; pseudo ; right ; vars ; skel ; ancs}

  let override ?ancs ?skel ?right ?left ?pseudo sq =
    mk_sequent ()
      ~left:(Option.default sq.left left)
      ~pseudo:(Option.default sq.pseudo pseudo)
      ?right:(Option.default sq.right right)
      ~skel:(Option.default sq.skel skel)
      ~ancs:(Option.default sq.ancs ancs)
end

include Sq

module Stats = struct
  type stats = {
    left_npreds : int IdtMap.t Lazy.t ;
    right_preds : Idt.t option ;
    left_nfuncs : int IdtMap.t Lazy.t ;
    right_nfuncs : int IdtMap.t Lazy.t ;
    left_dfuncs : int IdtMap.t Lazy.t ;
    right_dfuncs : int IdtMap.t Lazy.t ;
  }

  let map_leq ml mr =
    let ml = Lazy.force ml in
    let mr = Lazy.force mr in
    IdtMap.for_all begin fun l nl ->
      match IdtMap.find l mr with
      | nr -> nl <= nr
      | exception Not_found -> false
    end ml

  let right_leq l r =
    match l, r with
    | None, _ -> true
    | Some p, Some q -> p == q
    | _ -> false

  let leq stl str =
    right_leq stl.right_preds str.right_preds &&
    map_leq stl.left_npreds str.left_npreds &&
    map_leq stl.right_nfuncs str.right_nfuncs &&
    map_leq stl.left_nfuncs str.left_nfuncs &&
    map_leq stl.right_dfuncs str.right_dfuncs &&
    map_leq stl.left_dfuncs str.left_dfuncs

  let compare stl str =
    if leq stl str then
      if leq str stl then 0 else -1
    else +1

  let get l m =
    match IdtMap.find l m with
    | n -> n
    | exception Not_found -> 0

  let compute sq =
    let rec spin acc left =
      match Ft.front left with
      | None -> acc
      | Some (l, (p, _)) ->
          let acc =
            if Form.is_pseudo p then acc else
            IdtMap.add p (get p acc + 1) acc
          in
          spin acc l
    in
    let left_npreds = lazy (spin IdtMap.empty sq.left) in
    let right_preds = match sq.right with
      | Some (p, _) when not (Form.is_pseudo p) ->
          Some p
      | _ -> None
    in
    let rec walk_terms acc ts =
      match ts with
      | [] -> acc
      | t :: ts ->
          walk_terms (walk_term acc t) ts
    and walk_term acc t =
      match t.term with
      | Var _ | Idx _ -> acc
      | App (f, ts) ->
          let acc = IdtMap.add f (get f acc + 1) acc in
          walk_terms acc ts
    in
    let rec spin acc left =
      match Ft.front left with
      | None -> acc
      | Some (l, (p, ts)) ->
          let acc =
            if Form.is_pseudo p then acc else walk_terms acc ts
          in
          spin acc l
    in
    let left_nfuncs = lazy begin
      spin IdtMap.empty sq.left
    end in
    let right_nfuncs = lazy begin
      match sq.right with
      | Some (p, ts) when not (Form.is_pseudo p) ->
          walk_terms IdtMap.empty ts
      | _ -> IdtMap.empty
    end in
    let rec walk_term depth acc t =
      match t.term with
      | Var _ | Idx _ -> acc
      | App (f, ts) ->
          let acc = IdtMap.add f (max (get f acc) depth) acc in
          walk_terms (depth + 1) acc ts
    and walk_terms depth acc ts =
      match ts with
      | [] -> acc
      | t :: ts ->
          walk_terms depth (walk_term depth acc t) ts
    in
    let rec spin acc left =
      match Ft.front left with
      | None -> acc
      | Some (l, (p, ts)) ->
          let acc =
            if Form.is_pseudo p then acc else walk_terms 0 acc ts
          in
          spin acc l
    in
    let left_dfuncs = lazy (spin IdtMap.empty sq.left) in
    let right_dfuncs = lazy begin
      match sq.right with
      | Some (p, ts) when not (Form.is_pseudo p) ->
          walk_terms 0 IdtMap.empty ts
      | _ -> IdtMap.empty
    end in
    {left_npreds ; right_preds ;
     left_nfuncs ; right_nfuncs ;
     left_dfuncs ; right_dfuncs}

  let format ff stats =
    let open Format in
    let pp_map ff m = IdtMap.pp pp_print_int ff (Lazy.force m) in
    fprintf ff
      ("@[<v0>right_preds = %s@,left_npreds = %a@,left_nfuncs = %a@," ^^
       "right_nfuncs = %a@,left_dfuncs = %a@,right_nfuncs = %a@]")
      (match stats.right_preds with
       | None -> "."
       | Some p -> p.rep)
      pp_map stats.left_npreds
      pp_map stats.left_nfuncs
      pp_map stats.right_nfuncs
      pp_map stats.left_dfuncs
      pp_map stats.right_dfuncs
end

module StatMap = Map.Make (struct include Stats type t = stats end)

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

let subsume_ctx ~frz ~repl cx1 cx2 =
  let comparison_fn repl ts1 ts2 =
    Unify.unite_lists ~frz repl ts1 ts2 |> fst
  in
  Perms.superpose_maps comparison_fn repl cx1 cx2

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

let rec non_pseudo_length k l =
  match Ft.front l with
  | None -> k
  | Some (l, (p, _)) ->
      let k = if Form.is_pseudo p then k else k + 1 in
      non_pseudo_length k l

let subsume_test_left sl0 tl0 =
  non_pseudo_length 0 sl0 <= non_pseudo_length 0 tl0 &&
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
