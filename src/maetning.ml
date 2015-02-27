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
end

let options = Arg.(align [
    "-XX:EVCPseudos", Set Config.evc_pseudos, " Perform EVC on pseudos as well (default: false)" ;
    "-v", Int Config.set_verbosity, "<num> Set verbosity to <num>" ;
    "-version", Unit (fun () ->
        Printf.printf "Maetning version %s\n" Version.version ;
        Pervasives.exit 0
      ), " Display a version string" ;
    "-vnum", Unit (fun () ->
        Printf.printf "%s%!" Version.version ;
        Pervasives.exit 0
      ), " Display a version number (no newline at end)" ;
  ])
let parse_options () =
  let umsg = "Usage: maetning [options] file ..." in
  Arg.parse options Config.add_input_file umsg

let process_file file =
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
