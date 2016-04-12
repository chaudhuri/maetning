(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries

let listify fn ff l =
  let open Format in
  match l with
  | [] -> ()
  | [x] -> fn ff x
  | x :: xs ->
      fn ff x ;
      List.iter begin fun x ->
        pp_print_string ff " |" ;
        pp_print_space ff () ;
        fn ff x ;
      end xs

type dest =
  | Stderr
  | Stdout
  | File of file_dest

and file_dest = {
  filename       : string ;
  mutable ff     : Format.formatter ;
  mutable status : [`opened | `closed]
}

module StringMap = Map.Make(String)
let __dchans : dest StringMap.t ref = ref StringMap.empty

let on_stdout dchan =
  __dchans := StringMap.add dchan Stdout !__dchans

let on_stderr dchan =
  __dchans := StringMap.add dchan Stderr !__dchans

let on_file ~file dchan =
  let dest = File {filename = file ; ff = Format.err_formatter ; status = `closed} in
  __dchans := StringMap.add dchan dest !__dchans

let disable dchan =
  __dchans := StringMap.remove dchan !__dchans

let big_margin_fmt ff fmt =
  let marg = Format.pp_get_margin ff () in
  let maxind = Format.pp_get_max_indent ff () in
  let maxbox = Format.pp_get_max_boxes ff () in
  Format.pp_set_margin ff max_int ;
  Format.pp_set_max_indent ff max_int ;
  Format.pp_set_max_boxes ff max_int ;
  Format.kfprintf begin fun ff ->
    Format.pp_set_margin ff marg ;
    Format.pp_set_max_indent ff maxind ;
  Format.pp_set_max_boxes ff maxbox ;
  end ff fmt

let dprintf dchan =
  let uchan = String.map Char.uppercase dchan in
  match StringMap.find dchan !__dchans with
  | Stdout ->
      fun fmt ->
        big_margin_fmt Format.std_formatter ("[%s] " ^^ fmt) uchan
  | Stderr ->
      fun fmt ->
        big_margin_fmt Format.err_formatter ("[%s] " ^^ fmt) uchan
  | File fd ->
      if fd.status = `closed then begin
        fd.ff <- Format.formatter_of_output @@ File.open_out fd.filename ;
        fd.status <- `opened ;
      end ;
      Format.pp_set_margin fd.ff max_int ;
      Format.pp_set_max_indent fd.ff max_int ;
      fun fmt -> Format.fprintf fd.ff ("[%s] " ^^ fmt) uchan
  | exception Not_found -> Format.(ifprintf err_formatter)

let failwithf fmt =
  let open Format in
  let buf = Buffer.create 19 in
  let ff = formatter_of_buffer buf in
  kfprintf
    (fun ff -> pp_print_flush ff () ; failwith @@ Buffer.contents buf)
    ff fmt

exception Bug
let bugf fmt =
  Format.kfprintf (fun _ -> raise Bug) Format.err_formatter
    ("================================================================================@." ^^
     "!!! BUG !!!@." ^^
     "--------------------------------------------------------------------------------@." ^^
     fmt ^^ "@." ^^
     "--------------------------------------------------------------------------------@." ^^
     "Please report it at https://github.com/chaudhuri/maetning/issues@." ^^
     "================================================================================@.")
