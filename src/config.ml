(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)


let verbosity = ref 0
let set_verbosity n = verbosity := n

let input_files : string list ref = ref []
let add_input_file f = input_files := f :: !input_files
