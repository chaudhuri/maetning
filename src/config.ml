(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries

let set_debug_flags fls =
  String.nsplit fls ~by:"," |>
  List.iter begin fun fl ->
    match fl.[0] with
    | '-' -> Debug.disable @@ String.lchop ~n:1 fl
    | '+' -> Debug.on_stdout @@ String.lchop ~n:1 fl
    | _ -> Debug.on_stdout fl
  end

let () = set_debug_flags @@ String.concat "," [
    "label" ;
    "index" ;
    (* "rule" ; *)
    (* "select" ; *)
    (* "rulegen" ; *)
    (* "rulesub" ; *)
    (* "factor" ; *)
    (* "factgen" ; *)
    (* "subsumption" ; *)
    (* "stats" ; *)
    (* "skeleton" ; *)
    (* "reconstruct" ; *)
  ]

let input_files : string list ref = ref []
let add_input_file f = input_files := f :: !input_files

let evc_pseudos = ref false

let do_check = ref false

let show_shifts = ref false

let hide_bias = ref false

let shrink = ref true

let pseudo_proofs = ref true

let tptp = ref false

let rule_sub = ref false

let paranoia = ref false
let print_paranoia = false

let print_trail = ref false

let proof_formatter : Format.formatter option ref = ref None
let set_proof_channel filename =
  let oc = open_out_bin filename in
  let fmt = Format.formatter_of_out_channel oc in
  Format.pp_set_margin fmt max_int ;
  Format.pp_set_max_indent fmt max_int ;
  Format.fprintf fmt "%s@." {html|<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<style type="text/css">
  li { list-style-type: none ;
       list-style-image: url('https://google.github.io/material-design-icons/navigation/svg/ic_arrow_drop_down_24px.svg'); }
  ul { background-color: rgba(80,80,0,0.075); }
  pre { margin-left: 0em; color: #000080 ; }
  code { color: #000080 ; }
  h3 code { color: inherit ; }
  li table { vertical-align: top; display: inline-block; }
  td pre { margin: 0 0 ; padding: 0 0; }
  td.concl { border-top: 2px solid #000080; }
  p.pseudo { margin-left: 1em; color: red; font-weight: bold; }
</style>
<title>Proofs!</title>
</head>
<body>
|html} ;
  proof_formatter := Some fmt ;
  begin fun () ->
    Format.fprintf fmt "</body></html>@." ;
    close_out oc ;
    Printf.printf "Proofs are now available in %S.\n%!" filename ;
  end

let pprintf fmt =
  match !proof_formatter with
  | None -> Format.(ifprintf err_formatter fmt)
  | Some ff -> Format.(fprintf ff fmt)
