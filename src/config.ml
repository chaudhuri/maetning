(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries

let verbosity = ref 0
let set_verbosity n = verbosity := n

let input_files : string list ref = ref []
let add_input_file f = input_files := f :: !input_files

let evc_pseudos = ref false

let proof_formatter : Format.formatter option ref = ref None
let set_proof_channel filename =
  let oc = open_out_bin filename in
  let fmt = Format.formatter_of_out_channel oc in
  proof_formatter := Some fmt ;
  at_exit begin fun () ->
    Format.pp_print_flush fmt () ;
    close_out oc ;
  end
let printf fmt =
  match !proof_formatter with
  | None -> Format.(ifprintf err_formatter fmt)
  | Some ff -> Format.(fprintf ff fmt)
