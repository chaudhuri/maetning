(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Idt

type ty = {
  argtys : ty list ;
  target : idt ;
}

let basic b =
  { argtys = [] ; target = b }
let arrow tya tyb =
  { tyb with argtys = tya :: tyb.argtys }

let rec pretty_ty ty =
  let open Pretty in
  List.fold_right begin fun ta tb ->
    let ta = pretty_ty ta in
    Opapp (1, Infix (RIGHT, ta, FMT "->@ ", tb))
  end ty.argtys (Atom (STR ty.target.rep))

let format_ty ff ty = Pretty.print ff (pretty_ty ty)

let rec tyapp repl ty =
  let argtys = List.map (tyapp repl) ty.argtys in
  match IdtMap.find ty.target repl with
  | ty -> { ty with argtys = argtys @ ty.argtys }
  | exception Not_found -> { ty with argtys }

type tysig = {
  basics : IdtSet.t ;
  consts : ty IdtMap.t ;
}

(* Refinement *)

type free_term =
  | Fapp of idt * free_term list
  | Fty of idt

let rec split tysig targ =
  IdtMap.fold begin fun k kty cands ->
    if kty.target == targ then k :: cands else cands
  end tysig.consts [] |>
  List.map begin fun k ->
    let kty = IdtMap.find k tysig.consts in
    Fapp (k, List.map (fun ty -> Fty ty.target) kty.argtys)
  end

let rec cartesian_product ls =
  match ls with
  | [] -> []
  | [l] -> List.map (fun x -> [x]) l
  | l :: ls ->
      let ls = cartesian_product ls in
      List.map (fun x -> List.map (fun l -> x :: l) ls) l |> List.concat

let rec refine tysig ftm =
  match ftm with
  | Fty targ -> split tysig targ
  | Fapp (f, ftms) ->
      let frefs = List.map (refine tysig) ftms in
      cartesian_product frefs |>
      List.map (fun ftms -> Fapp (f, ftms))

module TestRef = struct
  let tynat = intern "nat"

  let tysig = {
    basics = IdtSet.singleton tynat ;
    consts = IdtMap.digest [ intern "z", basic tynat ;
                             intern "s", arrow (basic tynat) (basic tynat) ]
  }

  let doit () =
    refine tysig (Fapp (intern "s", [Fapp (intern "s", [Fty tynat])]))
end


(* type unification *)

let tyvargen = new Namegen.namegen Term.evar

let k_arrow = intern "->"

let rec thaw_wrt tysig repl (args, targ) =
  match args with
  | [] ->
      if IdtSet.mem targ tysig.basics
      then (repl, Term.app targ [])
      else begin
        let tv = match IdtMap.find targ repl with
          | tv -> tv
          | exception Not_found -> tyvargen#next
        in
        let repl = IdtMap.add targ tv repl in
        (repl, tv)
      end
  | arg :: args ->
      let (repl, tya) = thaw_wrt tysig repl (arg.argtys, arg.target) in
      let (repl, tyb) = thaw_wrt tysig repl (args, targ) in
      let ty = Term.app k_arrow [tya ; tyb] in
      (repl, ty)

let rec freeze ty =
  let open Term in
  match ty.term with
  | App (arr, [tya ; tyb]) when arr == k_arrow ->
      let tya = freeze tya in
      let tyb = freeze tyb in
      arrow tya tyb
  | App (k, []) ->
      basic k
  | _ ->
      failwith "freeze"

exception TyUnif

let unite_tys tysig tya tyb =
  try
    let repl = IdtMap.empty in
    let (repl, tya) = thaw_wrt tysig repl (tya.argtys, tya.target) in
    let (_, tyb) = thaw_wrt tysig repl (tyb.argtys, tyb.target) in
    let (_, tya) = Unify.unite Term.VMap.empty tya tyb in
    freeze tya
  with Unify.Unif _ -> raise TyUnif

module TestUnif = struct
  let tysig = {
    basics = IdtSet.of_list [intern "a" ; intern "b"] ;
    consts = IdtMap.empty ;
  }

  let tya = basic (intern "a")
  let tyb = basic (intern "b")
  let tyc = basic (intern "c")

  let ty1 = arrow tya tyb
  let ty2 = tyc

  let doit () = unite_tys tysig ty1 ty2
end
