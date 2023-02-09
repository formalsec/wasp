open Types
open Values
open Heap

let print_b_tree_keys (mem : memory) (n_keys : int) (max_keys : int) (node_addr : int) = 
  Printf.printf "[node: %s; keys: { " (string_of_int node_addr);
  for i = 0 to n_keys-1 do 
    let (v,sym) = load_value mem (Int64.of_int (node_addr+8+(4*i))) 0l I32Type in
    (*match sym with
      | Symvalue.Symbolic _ -> Printf.printf "%s " (Symvalue.to_string sym)
      | _ -> Printf.printf "%s " (string_of_value v)*)

    Printf.printf "%s " (Symvalue.to_string sym)
  done;
  let i = ref n_keys in
  while !i < max_keys do
    Printf.printf " ";
    i := !i+1
  done; 
  Printf.printf "}]";
  Printf.printf "\t"

let rec print_b_tree_level_order (n : int list) (mem : memory) (max_keys : int) =
  let next = ref [] in
  for i = 0 to (List.length n)-1 do
    (*let (num_keys,_,_) = Hashtbl.find mem ((List.nth n i)+4) in*)
    let (num_keys,_) = load_value mem (Int64.of_int ((List.nth n i)+4)) 0l I32Type in
    print_b_tree_keys mem (int_of_string (string_of_value num_keys)) max_keys (List.nth n i);
    (*let (leaf,_,_) = Hashtbl.find mem (List.nth n i) in*)
    let (leaf,_) = load_value mem (Int64.of_int (List.nth n i)) 0l I32Type in
    if (int_of_string (string_of_value leaf)) = 0 then (
      for j = 0 to (int_of_string (string_of_value num_keys)) do (* children *)
        (*let (value,_,_) = Hashtbl.find mem (((List.nth n i))+8+(4*max_keys)+(4*j)) in*)
        let (value,_) = load_value mem (Int64.of_int (((List.nth n i))+8+(4*max_keys)+(4*j))) 0l I32Type in
        next := !next @ [(int_of_string (string_of_value value))]
      done
    )
  done;
  Printf.printf "\n";
  if !next <> [] then print_b_tree_level_order !next mem max_keys

(*  String representation of the btree on the logical environment  *)
let print_b_tree (mem : memory) = 
  (*let (root_addr,_,_) = Hashtbl.find mem 8 in*)
  let (root_addr,_) = load_value mem (Int64.of_int 8) 0l I32Type in
  (*let (t,_,_) = Hashtbl.find mem 0 in*)
  let (t,_) = load_value mem (Int64.of_int 0) 0l I32Type in
  let max_keys = (int_of_string (string_of_value t))-1 in
  (*let (n_keys,_,_) = Hashtbl.find mem ((int_of_string (string_of_value root_addr))+4) in*)
  let (n_keys,_) = load_value mem (Int64.of_int ((int_of_string (string_of_value root_addr))+4)) 0l I32Type in
  print_b_tree_keys mem (int_of_string (string_of_value n_keys)) max_keys (int_of_string (string_of_value root_addr));
  Printf.printf("\n");

  let children = ref [] in
  (*let (leaf,_,_) = Hashtbl.find mem (int_of_string (string_of_value root_addr)) in*)
  let (leaf,_) = load_value mem (Int64.of_string (string_of_value root_addr)) 0l I32Type in
  if (int_of_string (string_of_value leaf)) = 0 then (
    for i = 0 to (int_of_string (string_of_value n_keys)) do (* children *)
      (*let (value,_,_) = Hashtbl.find mem ((int_of_string (string_of_value root_addr))+8+(4*((int_of_string (string_of_value t))-1))+(4*i)) in*)
      let (value,_) = load_value mem (Int64.of_int ((int_of_string (string_of_value root_addr))+8+(4*((int_of_string (string_of_value t))-1))+(4*i))) 0l I32Type in
      children := !children @ [(int_of_string (string_of_value value))]
    done);
