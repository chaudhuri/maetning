(* See LICENSE for licensing details. *)

(* BEGIN VERSION *)
let major_version  : int           = 0
let minor_version  : int           = 5
let patch_version  : int           = 0
let flavor_version : string option = None
(* END VERSION *)

let version_string =
  Printf.sprintf "%d.%d.%d%s" major_version minor_version patch_version
    (match flavor_version with
     | Some v -> "-" ^ v
     | None -> "")

let version_file_contents =
  let buf = Buffer.create 255 in
  let printf fmt = Printf.bprintf buf (fmt ^^ "\n") in
  printf "(* DO NOT EDIT *)" ;
  printf "(* this file is automatically generated by myocamlbuild.ml *)" ;
  printf "let major : int = %d;;" major_version ;
  printf "let minor : int = %d;;" minor_version ;
  printf "let patch : int = %d;;" patch_version ;
  printf "let flavor : string option = %s;;" begin
    match flavor_version with
    | None -> "None"
    | Some v -> "Some \"" ^ String.escaped v ^ "\""
  end ;
  printf "let version = %S;;" version_string ;
  Buffer.contents buf

let version_file = "src/version.ml"

let maybe_make_version_file () =
  if not begin
      Sys.file_exists version_file
      && Digest.file version_file = Digest.string version_file_contents
    end then begin
    Printf.printf "Recreating %S\n" version_file ;
    let oc = open_out version_file in
    output_string oc version_file_contents ;
    close_out oc
  end

let () =
  maybe_make_version_file () ;
  Ocamlbuild_plugin.(
    Options.use_ocamlfind := true ;
    Options.use_menhir := true ;
    dispatch begin function
    | After_rules ->
        (* flag ["ocaml" ; "compile"] (A "-g") ; *)
        flag ["ocaml" ; "menhir"] (S [A "--explain" ; A "--strict"]) ;
        flag ["ocaml" ; "compile"] (A "-bin-annot") ;
        flag ["ocaml" ; "compile"] (A "-safe-string") ;
        flag ["ocaml" ; "link"] (A "-safe-string") ;
        (* flag ["ocaml" ; "link"] (A "-g") ; *)
        flag ["ocaml" ; "compile"] (S [A "-w" ; A "@3@5@6@8..12@14@20@26@28@29"]) ;
        flag ["ocaml" ; "native" ; "compile"] (A "-nodynlink") ;
    | _ -> ()
    end
  )
