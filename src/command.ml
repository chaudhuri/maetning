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
  polarity_map := IdtMap.add idt pol !polarity_map

let default_polarity = NEG
let lookup_polarity idt =
  IdtMap.find_opt idt !polarity_map |>
  Option.default default_polarity

let add_global x f = ()
let add_pseudo x f = ()
let retract x = ()
let prove f = ()
let refute f = ()
