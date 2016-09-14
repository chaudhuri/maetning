(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014,2015  Inria
 *     (Institut National de Recherche en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries

module M = Model

let set_output file =
  let disch = Config.set_proof_channel file in
  at_exit disch

let set_dump file =
  match file with
  | "-" | "'-'" ->
      Config.dump_database := Some Format.std_formatter
  | _ ->
      Config.dump_database := Some (Format.formatter_of_output (open_out file))

let set_dependency_dag file =
  let ff = Format.formatter_of_output (open_out file) in
  Format.fprintf ff "digraph sequents {@." ;
  at_exit (fun () -> Format.fprintf ff "}@.") ;
  Config.dependency_dag := Some ff

let options = Arg.(align [
    "", Unit (fun () -> ()), " \n\t*** INPUT ***\n" ;
    "-tptp", Set Config.tptp, " Assume input files are in TPTP/ILTP format (only supports FOF)" ;
    "", Unit (fun () -> ()), " \n\t*** OUTPUT ***\n" ;
    "-proofs", String set_output, "<file> Output proofs/models to <file> (in HTML format)" ;
    "-dotmodels", Set Config.dot_models, " Use dot(1) to prettify models" ;
    "-shifts", Set Config.show_shifts, " Show polarity shifts" ;
    "-nobias", Set Config.hide_bias, " Hide predicate biases" ;
    "-noshrink", Clear Config.shrink, " Do not shrink proofs down to relevant details" ;
    "-dump", String set_dump, "<file> Dump the final sequent database to <file> (use - for stdout)" ;
    "-dep", String set_dependency_dag, "<file> Dump the sequent dependency graph to <file>" ;
    "", Unit (fun () -> ()), " \n\t*** CONSISTENCY ***\n" ;
    "-check", Set Config.do_check, " Reconstruct a full proof from the skeleton and check it" ;
    "-paranoia", Set Config.paranoia, " Check every indexed sequent" ;
    "-nopseudos", Clear Config.pseudo_proofs, " Do not reconstruct pseudo proofs" ;
    "", Unit (fun () -> ()), " \n\t*** DEBUG ***\n" ;
    "-timeout", Int Config.set_timeout, "<millis> Set a (soft) timeout in milliseconds" ;
    "-debug", String Config.set_debug_flags, "<flags> Enable debug flags <flags>, comma-separated" ;
    "", Unit (fun () -> ()), " \t(A flag is an identifier prefixed by + or -.)" ;
    "-XX:EVCPseudos", Set Config.evc_pseudos, " Perform EVC on pseudos as well (default: false)" ;
    "", Unit (fun () -> ()), " \n\t*** MISCELLANEOUS ***\n" ;
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
  let umsg = Printf.sprintf "Usage: %s [options] file ..." (Filename.basename Sys.executable_name) in
  Arg.parse options Config.add_input_file umsg

let process_file_native file =
  Config.pprintf "<h3>Proofs/models from <code>%s</code></h3>@.<hr>@." file ;
  let ch = open_in_bin file in
  let lb = Lexing.from_channel ch in
  Front_parse.file Front_lex.token lb ;
  close_in ch

let rec process_file_tptp file =
  Config.pprintf "<h3>Proofs/models from <code>%s</code></h3>@.<hr>@." file ;
  let ch = open_in_bin file in
  let lb = Lexing.from_channel ch in
  let rec spin () =
    match Tptp_parse.tptp_input Tptp_lex.token lb with
    | `Form (name, role, f) -> begin
        match role.Idt.rep with
        | "axiom" -> Command.add_global name f
        | "hypothesis" -> Command.add_global name f
        | "lemma" -> failwith "Lemmas not supported"
        | "conjecture" | "prove" -> Command.prove f
        | "refute" -> Command.refute f
        | "pseudo" -> Command.add_pseudo name f
        | role -> failwith ("Role " ^ role ^ " not understood")
      end ; spin ()
    | `Include (file, _) ->
        process_file_tptp file ; spin ()
    | exception Tptp_parse.Error -> ()
    | exception Tptp_lex.EOS -> ()
  in
  spin () ; close_in ch

let process_file file =
  if !Config.tptp
  then process_file_tptp file
  else process_file_native file

let main () =
  parse_options () ;
  List.iter process_file (List.rev !Config.input_files)

let () =
  if not !Sys.interactive then
    main () ;;
