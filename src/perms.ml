open Batteries

open Idt

type dir = L | R | S

let cand posns dirs =
  let open Array in
  let ret = ref (-1) in
  for i = 0 to Array.length posns - 1 do
    if unsafe_get dirs i <> S then
      if !ret = -1 || unsafe_get posns !ret < unsafe_get posns i then
        ret := i
  done ;
  !ret

exception Permutations_done

let move posns dirs =
  let open Array in
  let n = length posns in
  let i = cand posns dirs in
  if i = -1 then raise Permutations_done else
  let i = match dirs.(i) with
  | S -> Debug.bugf "Perms.move"
  | L ->
      let tmp = unsafe_get posns i in
      unsafe_set posns i (unsafe_get posns (i - 1)) ;
      unsafe_set posns (i - 1) tmp ;
      let tmp = unsafe_get dirs i in
      unsafe_set dirs i (unsafe_get dirs (i - 1)) ;
      unsafe_set dirs (i - 1) begin
        if i = 1 ||
           (i > 1 && unsafe_get posns (i - 2) > unsafe_get posns (i - 1))
        then S
        else tmp
      end ;
      i - 1
  | R ->
      let tmp = unsafe_get posns i in
      unsafe_set posns i (unsafe_get posns (i + 1)) ;
      unsafe_set posns (i + 1)tmp ;
      let tmp = unsafe_get dirs i in
      unsafe_set dirs i (unsafe_get dirs (i + 1)) ;
      unsafe_set dirs (i + 1) begin
        if i = n - 2 ||
           (i < n - 2 && unsafe_get posns (i + 2) > unsafe_get posns (i + 1))
        then S
        else tmp
      end ;
      i + 1
  in
  for j = 0 to n - 1 do
    if j <> i && unsafe_get posns j > unsafe_get posns i then
      unsafe_set dirs j (if j < i then R else L)
  done

let iter fn l =
  match l with
  | [] ->
      fn l
  | x :: _ ->
      let n = List.length l in
      let elems = Array.of_list l in
      let posns = Array.init n (fun i -> i) in
      let dirs = Array.make n L in
      Array.unsafe_set dirs 0 S ;
      let snap () = Array.fold_right (fun e l -> Array.unsafe_get elems e :: l) posns [] in
      let rec spin () =
        fn (snap ()) ;
        match move posns dirs with
        | () -> spin ()
        | exception Permutations_done -> ()
      in
      spin ()

module Test = struct
  let show_perms l =
    let count = ref 1 in
    l |>
    iter begin fun l ->
      print_int !count ;
      print_string " " ;
      incr count ;
      l |>
      List.map string_of_int |>
      String.concat "," |>
      print_endline
    end
end

type ptree =
  | Node of (int * ptree Lazy.t) list

let ptree m n =
  if n = 0 then Node [] else
  let rec spin i avail =
    if i >= m then Node [] else
    let pts = ref [] in
    for j = 0 to n - 1 do
      if BitSet.mem avail j then begin
        let avail = BitSet.remove j avail in
        let pt = lazy (spin (i + 1) avail) in
        ignore (Lazy.force pt) ;
        pts := (j, pt) :: !pts
      end
    done ;
    Node (List.rev !pts)
  in
  spin 0 (BitSet.create_full n)

exception Incompatible

let superpose fn (acc : 'acc) tss1 tss2 : 'acc list =
  let tss1 = Array.of_list tss1 in
  let tss2 = Array.of_list tss2 in
  if Array.length tss1 > Array.length tss2 then raise Incompatible ;
  let ptr = ptree (Array.length tss1) (Array.length tss2) in
  let rec process ~i ~acc (Node choices) =
    List.map begin fun (j, conseq) ->
      match fn acc tss1.(i) tss2.(j) with
      | acc -> process ~i:(i + 1) ~acc (Lazy.force conseq)
      | exception _ -> []
    end choices |>
    List.concat
  in
  process ~i:0 ~acc ptr

let rec superpose_maps fn (acc : 'acc) m1 m2 : 'acc =
  let ((p, tss1), m1) = IdtMap.pop m1 in
  let tss2 = match IdtMap.find p m2 with
    | tss2 -> tss2
    | exception Not_found -> []
  in
  let choices = superpose fn acc tss1 tss2 in
  let rec scan_choices choices =
    match choices with
    | [] -> raise Incompatible
    | acc :: choices -> begin
        match superpose_maps fn acc m1 m2 with
        | acc -> acc
        | exception Incompatible -> scan_choices choices
      end
  in
  scan_choices choices
