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

let polarity_map : Form.polarity IdtMap.t ref = ref IdtMap.empty

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

let global_map : Form.form IdtMap.t ref = ref IdtMap.empty
let pseudo_map : Form.form IdtMap.t ref = ref IdtMap.empty

let ensure_new x =
  if IdtMap.mem x !global_map ||
     IdtMap.mem x !pseudo_map ||
     IdtMap.mem x !polarity_map
  then begin
    Format.eprintf "Name %S already used..@." x.rep ;
    failwith "ensure_new"
  end

let add_global x f =
  ensure_new x ;
  let f = force NEG f in
  global_map := IdtMap.add x f !global_map ;
  Format.printf "Added global: %a.@." (Form.format_form ()) f

let add_pseudo x f =
  ensure_new x ;
  let f = force NEG f in
  pseudo_map := IdtMap.add x f !pseudo_map ;
  Format.printf "Added pseudo: %a.@." (Form.format_form ()) f

let retract x =
  if IdtMap.mem x !global_map then
    global_map := IdtMap.remove x !global_map
  else
    pseudo_map := IdtMap.remove x !pseudo_map

let values map =
  IdtMap.fold (fun _ v l -> v :: l) map []

type result = Proved
            | Refuted
            | Unsound of Idt.t

let setup f =
  let open Sequent in
  let f = force POS f in
  (* Format.printf "Goal: %a.@." (Form.format_form ()) f ; *)
  let globals = values !global_map in
  let pseudo = values !pseudo_map in
  match Inverse.inverse_method ~left:globals ~pseudo:pseudo f with
  | None -> Refuted
  | Some pf -> begin
      match
        Ft.to_list pf.left |>
        List.Exceptionless.find (fun (p, _) -> Form.is_pseudo p)
      with
      | None -> Proved
      | Some (p, _) -> Unsound p
    end

let prove f =
  match setup f with
  | Proved -> Format.printf "Proved.@."
  | Refuted -> failwith "Not provable"
  | Unsound p -> Format.printf "UNKNOWN: pseudo %s was used.@." p.rep

let refute f =
  match setup f with
  | Proved -> failwith "Not refuted"
  | Refuted -> Format.printf "Refuted.@."
  | Unsound p -> Format.printf "UNKNOWN: pseudo %s was used.@." p.rep
