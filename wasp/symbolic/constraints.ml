(*
░█████╗░░█████╗░███╗░░██╗░██████╗████████╗██████╗░░█████╗░██╗███╗░░██╗████████╗░██████╗
██╔══██╗██╔══██╗████╗░██║██╔════╝╚══██╔══╝██╔══██╗██╔══██╗██║████╗░██║╚══██╔══╝██╔════╝
██║░░╚═╝██║░░██║██╔██╗██║╚█████╗░░░░██║░░░██████╔╝███████║██║██╔██╗██║░░░██║░░░╚█████╗░
██║░░██╗██║░░██║██║╚████║░╚═══██╗░░░██║░░░██╔══██╗██╔══██║██║██║╚████║░░░██║░░░░╚═══██╗
╚█████╔╝╚█████╔╝██║░╚███║██████╔╝░░░██║░░░██║░░██║██║░░██║██║██║░╚███║░░░██║░░░██████╔╝
░╚════╝░░╚════╝░╚═╝░░╚══╝╚═════╝░░░░╚═╝░░░╚═╝░░╚═╝╚═╝░░╚═╝╚═╝╚═╝░░╚══╝░░░╚═╝░░░╚═════╝░    *)


(*  Stores the AssumeFail constraints  *)
type constraints = (int, Symvalue.sym_expr list) Hashtbl.t

(*  Creates a hashtable to store the AssumeFail constraints  *)
let create_constraints : constraints = 
	let const : constraints = Hashtbl.create 510 in
	const

(*  Adds a variable to the AssumeFail constraints  *)
let set_constraint (const : constraints) (iteration : int) 
    (lst : Symvalue.sym_expr list) : unit =
  Hashtbl.replace const iteration lst

(*  String representation of the AssumeFail constraints  *)
let print_constraints (const : constraints) : string = 
	Hashtbl.fold (fun k v acc -> 
    "[  Iteration #" ^ (string_of_int k) ^ 
    "    ---->    "  ^ (Symvalue.pp_string_of_pc v) ^
    "  ]\n" ^ acc
  ) const ""
