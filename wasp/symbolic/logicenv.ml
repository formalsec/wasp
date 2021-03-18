open Values
open Symvalue

(*  Stores the concrete values assigned to symbolic variables  *)
type logical_env = (string, value) Hashtbl.t

(*  Create a logical environment  *)
let create_logic_env (var_vals : (string * value) list) : logical_env = 
	let env : logical_env = Hashtbl.create 512 in
	List.iter (fun (x, y) -> Hashtbl.add env x y) var_vals;
	env

(*  Adds a variable to the logical environment  *)
let set_sym (env : logical_env) (var : string) (value : value) : unit = 
  Hashtbl.replace env var value

(*  Gets a variable from the logical environment  *)
let get_sym (env : logical_env) (var : string) : value = 
  Hashtbl.find env var 

let is_empty (env : logical_env) : bool =
  (Hashtbl.length env) = 0

(*  String representation of the logical environment  *)
let print_sym_store (env : logical_env) : string = 
	Hashtbl.fold (fun k v acc -> "(" ^ k ^ "->" ^ (string_of_value v) ^ ")\n" ^ acc) env ""

(*  Get the names of the symbolic variables that are integers  *)
let get_sym_int32_vars (env : logical_env) : string list = 
	Hashtbl.fold (fun k v acc -> 
		match v with
			| I32 _ -> [k] @ acc
			| _ -> acc
	) env []

(*  Get the names of the symbolic variables that are integers  *)
let get_sym_int64_vars (env : logical_env) : string list = 
	Hashtbl.fold (fun k v acc -> 
		match v with
			| I64 _ -> [k] @ acc
			| _ -> acc
	) env []

(*  Get the names of the symbolic variables that are floats  *)
let get_sym_float32_vars (env : logical_env) : string list = 
	Hashtbl.fold (fun k v acc -> 
		match v with
			| F32 _ -> [k] @ acc
			| _ -> acc
	) env []

(*  Get the names of the symbolic variables that are floats  *)
let get_sym_float64_vars (env : logical_env) : string list = 
	Hashtbl.fold (fun k v acc -> 
		match v with
			| F64 _ -> [k] @ acc
			| _ -> acc
	) env []

let neg_pc (env : logical_env) : sym_expr =
  Hashtbl.fold (fun k v acc ->
    let e = 
      match v with
      | I32 _ -> I32Relop (Si32.I32Neq, Value v, (Symbolic (SymInt32, k)))
      | I64 _ -> I64Relop (Si64.I64Neq, Value v, (Symbolic (SymInt64, k)))
      | F32 _ -> F32Relop (Sf32.F32Neq, Value v, (Symbolic (SymFloat32, k)))
      | F64 _ -> F64Relop (Sf64.F64Neq, Value v, (Symbolic (SymFloat64, k)))
    in BoolOp (Or, e, acc)
  ) env (I32Relop (Si32.I32Eq, Value (I32 0l), Value (I32 1l)))
