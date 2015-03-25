(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014,2015  Inria
 *     (Institut National de Recherche en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries

module Deps = struct
  open Term
  open Unify
  open Form
  open Sequent
  open Rule
  open Rule_gen
  open Inverse
  open Front_parse
  open Front_lex
  open Agencies
  open Seqproof_print
  open Counter
end

let set_input file =
  let disch = Config.set_proof_channel file in
  at_exit disch

let options = Arg.(align [
    "-check", Set Config.do_check, " Reconstruct a full proof from the skeleton and check it" ;
    "-proofs", String set_input, "<file> Output proofs to <file> (in HTML format)" ;
    "-version", Unit (fun () ->
        Printf.printf "Maetning version %s\n" Version.version ;
        Pervasives.exit 0
      ), " Display a version string" ;
    "-vnum", Unit (fun () ->
        Printf.printf "%s%!" Version.version ;
        Pervasives.exit 0
      ), " Display a version number (no newline at end)" ;
    "-XX:EVCPseudos", Set Config.evc_pseudos, " Perform EVC on pseudos as well (default: false)" ;
  ])
let parse_options () =
  let umsg = "Usage: maetning [options] file ..." in
  Arg.parse options Config.add_input_file umsg

let process_file file =
  Config.pprintf "<h3>Proofs from <code>%s</code></h3>@." file ;
  let ch = open_in_bin file in
  let lb = Lexing.from_channel ch in
  Front_parse.file Front_lex.token lb ;
  close_in ch

let main () =
  parse_options () ;
  List.iter process_file !Config.input_files

let () =
  if not !Sys.interactive then
    main () ;;
