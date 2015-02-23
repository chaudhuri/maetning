(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014  INRIA (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Term
open Unify
open Form
open Sequent
open Rule

let () =
  if not !Sys.interactive then
    print_endline Version.version ;;
