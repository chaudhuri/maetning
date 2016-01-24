(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2016  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries

class fout ?preamble ?postamble () =
  object (self)
    val mutable conn : (Format.formatter * unit BatIO.output) option = None

    val mutable dispose = fun () -> ()

    method private reinit =
      dispose <- begin fun () ->
        match conn with
        | None -> ()
        | Some (ff, oc) ->
            begin match postamble with
            | Some fn -> fn ff
            | _ -> ()
            end ;
            Format.pp_print_flush ff () ;
            close_out oc
      end ;
      begin match conn, preamble with
      | Some (ff, _), Some fn -> fn ff
      | _ -> ()
      end

    method connect filename =
      dispose () ;
      let oc = open_out filename in
      let ff = Format.formatter_of_output oc in
      conn <- Some (ff, oc) ;
      self#reinit

    method printf : 'a. ('a, Format.formatter, unit) format -> 'a =
      fun fmt -> match conn with
        | None -> Format.(ifprintf err_formatter fmt)
        | Some (ff, _) -> Format.(fprintf ff fmt)

    initializer begin
      at_exit (fun () -> dispose ())
    end
  end
