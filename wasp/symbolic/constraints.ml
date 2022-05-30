open Symvalue

(*  Stores the AssumeFail constraints  *)
type constraints = (int, path_conditions) Hashtbl.t
type t = constraints

(*  Creates a hashtable to store the AssumeFail constraints  *)
let create : constraints =
  let c : constraints = Hashtbl.create 512 in
  c

let add (c : constraints) (i : int) (pc : path_conditions) : unit =
  Hashtbl.replace c i pc

let to_string (c : constraints) : string =
  let lst = Hashtbl.fold (fun k v acc -> (k, v) :: acc) c [] in
  let lst = List.sort (fun (a, _) (b, _) -> compare a b) lst in
  List.fold_left (fun a (k, v) ->
    a ^ "[  Iteration #" ^ (string_of_int k) ^
        "    ---->    "  ^ (Symvalue.pp_string_of_pc v) ^ "]\n"
  ) "" lst
