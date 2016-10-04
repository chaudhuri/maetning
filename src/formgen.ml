(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2016  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Generate a random formula *)

open Batteries
open Form

let () = Random.self_init ()

let rec generate ?(maxdepth=10) atoms =
  let natoms = Array.length atoms in
  if maxdepth = 0 then begin
    match Random.int 3 with
    (* | 0 -> *)
    (*     let pol = if Random.int 2 = 0 then POS else NEG in *)
    (*     conj ~pol [] *)
    (* | 1 -> disj [] *)
    | _ ->
        let k = Random.int natoms in
        let (pol, a) = Array.unsafe_get atoms k in
        atom pol a []
  end else begin
    let maxdepth = maxdepth - 1 in
    match Random.int 6 with
    | 0 ->
        generate ~maxdepth:0 atoms
    | 1 ->
        let pol = if Random.int 2 = 0 then POS else NEG in
        conj ~pol [generate ~maxdepth atoms ; generate ~maxdepth atoms]
    | 2 ->
        disj [generate ~maxdepth atoms ; generate ~maxdepth atoms]
    | 3 ->
        implies [generate ~maxdepth atoms] (generate ~maxdepth atoms)
    | 4 ->
        implies [generate ~maxdepth atoms] (disj [])
    | _ ->
        shift (generate ~maxdepth atoms)
  end

module Test = struct
  let test ?file ~maxdepth ~atoms n =
    begin match file with
    | Some file ->
        let disch = Config.set_proof_channel file in
        at_exit disch
    | None -> ()
    end ;
    Config.show_shifts := false ;
    Config.do_check := true ;
    Config.dot_models := true ;
    for i = 0 to n do
      let f = generate ~maxdepth atoms in
      Format.printf "═════════════════════════════════════════════════════════════════@." ;
      Format.printf "Testing: %a@." format_form f ;
      Format.printf "═════════════════════════════════════════════════════════════════@." ;
      begin try ignore (Command.prove f) with Failure _ -> () end
    done

  let main () =
    let maxdepth = ref 5 in
    let ntests = ref 20 in
    let file = ref None in
    let atoms = ref [| POS, Idt.intern "a" ; NEG, Idt.intern "b" |] in
    let to_pol atm =
      match atm.[String.length atm - 1] with
      | '+' -> POS, Idt.intern (String.rchop ~n:1 atm)
      | '-' -> NEG, Idt.intern (String.rchop ~n:1 atm)
      | _ -> POS, Idt.intern atm
    in
    let set_atoms atms =
      atoms :=
        atms |>
        BatString.nsplit ~by:"," |>
        List.map to_pol |>
        Array.of_list
    in
    let opts = Arg.(align [
        "-a", String set_atoms, "<atoms> Use given comma-separated <atoms> list (default: a+,b-)" ;
        "-n", Int (fun k -> ntests := k), "<num> Run <num> tests (default: 20)" ;
        "-d", Int (fun d -> maxdepth := d), "<num> Set max formula depth to <num>" ;
        "-f", String (fun s -> file := Some s), "<file> Output results to <file>" ;
      ]) in
    let umsg =
      Printf.sprintf "Usage: %s [options]" (Filename.basename Sys.executable_name) in
    Arg.parse opts (fun s -> ()) umsg ;
    Format.printf "Running %d tests@." !ntests ;
    Format.printf "Using atoms: %s@."
      (!atoms |> Array.to_list |>
       List.map begin fun (pol, id) ->
         id.Idt.rep ^ (if pol = POS then "+" else "-")
       end |> String.concat ", ") ;
    test ?file:!file ~maxdepth:!maxdepth ~atoms:!atoms !ntests
end

let () =
  if not !Sys.interactive then Test.main ()
