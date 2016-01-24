(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2016  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Model reconstruction based on the algorithm described in:

   Taus Brock-Nannestad and Kaustuv Chaudhuri, "Saturation-based
   Countermodel Construction for Propositional Intuitionistic Logic",
   2016
*)

open Batteries
module Ft = FingerTree

open Idt
open Term
open Form
open Sequent
open Inverse

open Debug

type model =
  | Leaf of constr
  | Fork of constr * model list

and constr = {
  live : form list ;            (* all T *)
  dead : form list ;            (* all T *)
  fals : form option ;          (* all F *)
}

let first_order () =
  Debug.bugf "Cannot construct countermodels for first-order formulas"

let format_constr ff constr =
  let open Format in
  pp_open_box ff 2 ; begin
    pp_print_string ff "[[ " ;
    List.iter begin fun f ->
      fprintf ff "T(@[%a@])@ " (format_form ()) f
    end constr.live ;
    List.iter begin fun f ->
      fprintf ff "T*(@[%a@])@ " (format_form ()) f
    end constr.dead ;
    begin match constr.fals with
    | Some f ->
        fprintf ff "F(%a)@ " (format_form ()) f
    | None -> ()
    end ;
    pp_print_string ff "]]" ;
  end ; pp_close_box ff ()


(* query the oracle *)
let query constr =
  let rec right_active ~left right =
    match right with
    | None -> left_active ~left None
    | Some rf -> begin
        match rf.form with
        | Atom (POS, l, [])
        | Shift {form = Atom (POS, l, []) ; _} ->
            left_active ~left (Some l)
        | And (NEG, rf1, rf2) ->
            right_active ~left (Some rf1) @
            right_active ~left (Some rf2)
        | True NEG ->
            []
        | Implies (rf1, rf2) ->
            right_active ~left:(rf1 :: left) (Some rf1)
        | Forall _ -> first_order ()
        | _ ->
            Debug.bugf "Model.query(right_active}: Impossible @[%a@]"
              (format_form ()) rf
      end
  and left_active ?(stored = []) ~left right =
    match left with
    | [] ->
        [mk_sequent ()
           ~left:(stored |>
                  List.map (fun l -> (l, [])) |>
                  Ft.of_list)
           ?right:(right |> Option.map (fun l -> (l, [])))]
    | lf :: left -> begin
        match lf.form with
        | Atom (NEG, l, [])
        | Shift {form = Atom (NEG, l, []) ; _} ->
            left_active ~stored:(l :: stored) ~left right
        | And (POS, lf1, lf2) ->
            left_active ~stored ~left:(lf1 :: lf2 :: left) right
        | True POS ->
            left_active ~stored ~left right
        | Or (lf1, lf2) ->
            left_active ~stored ~left:(lf1 :: left) right @
            left_active ~stored ~left:(lf2 :: left) right
        | False ->
            []
        | Exists _ -> first_order ()
        | _ ->
            Debug.bugf "Model.query(left_active}: Impossible @[%a@]"
              (format_form ()) lf
      end
  in
  dprintf "modelquery" "Querying @[%a@]@." format_constr constr ;
  let sequents = right_active ~left:(constr.live @ constr.dead) constr.fals in
  List.iter begin fun sq ->
    dprintf "modelquery" "Need to check: @[%a@]@." (format_sequent ()) sq
  end sequents
