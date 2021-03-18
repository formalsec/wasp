open Si32
open Si64
open Sf32
open Sf64
open Values

type symbolic = SymInt32 | SymInt64 | SymFloat32 | SymFloat64

type boolop = And | Or

type sym_expr = 
  (* Value *)
  | Value    of value
	(* I32 operations *)
  | I32Binop of Si32.binop * sym_expr * sym_expr
	| I32Unop  of Si32.unop  * sym_expr
	| I32Relop of Si32.relop * sym_expr * sym_expr
	(* I64 operations *)
	| I64Binop of Si64.binop * sym_expr * sym_expr
	| I64Unop  of Si64.unop  * sym_expr
	| I64Relop of Si64.relop * sym_expr * sym_expr
	(* F32 operations *)
	| F32Binop of Sf32.binop * sym_expr * sym_expr
	| F32Unop  of Sf32.unop  * sym_expr
	| F32Relop of Sf32.relop * sym_expr * sym_expr
	(* F64 operations *)
	| F64Binop of Sf64.binop * sym_expr * sym_expr
	| F64Unop  of Sf64.unop  * sym_expr
	| F64Relop of Sf64.relop * sym_expr * sym_expr
	(* Symbolic *)
	| Symbolic of symbolic * string
  (* Encoding Auxiliary *)
  | Extract  of sym_expr * int
  | Concat   of sym_expr * sym_expr
  | BoolOp   of boolop   * sym_expr * sym_expr

(*  Pair ( (concrete) Value, (symbolic) Expression)  *)
type sym_value = value * sym_expr

(*  To keep record of the path conditions  *)
type path_conditions = sym_expr list

let size = function
  | SymInt32 | SymFloat32 -> 32
  | SymInt64 | SymFloat64 -> 64

(*  Negates a sym_expr  *)
let rec neg_expr (e : sym_expr) : sym_expr =
  begin match e with 
	(* I32 *)
  | I32Relop (I32Eq, e1, e2) -> I32Relop (I32Neq, e1, e2) 
  | I32Relop (I32Neq, e1, e2) -> I32Relop (I32Eq, e1, e2)
  | I32Relop (I32Lt, e1, e2) -> I32Relop (I32GtEq, e1, e2)
  | I32Relop (I32Gt, e1, e2) -> I32Relop (I32LtEq, e1, e2)
  | I32Relop (I32LtEq, e1, e2) -> I32Relop (I32Gt, e1, e2)
  | I32Relop (I32GtEq, e1, e2) -> I32Relop (I32Lt, e1, e2)
  | I32Binop (op, e1, e2) ->
      begin match op with
		  | I32And -> I32Binop (I32Or, (neg_expr e1), (neg_expr e2))
	    | I32Or -> I32Binop (I32And, (neg_expr e1), (neg_expr e2))
		  | _ -> I32Relop (I32Eq, e, (Value (I32 0l)))
      end
	(* I64 *)
	| I64Relop (I64Eq, e1, e2) -> I64Relop (I64Neq, e1, e2) 
	| I64Relop (I64Neq, e1, e2) -> I64Relop (I64Eq, e1, e2)
	| I64Relop (I64Lt, e1, e2) -> I64Relop (I64GtEq, e1, e2)
	| I64Relop (I64Gt, e1, e2) -> I64Relop (I64LtEq, e1, e2)
	| I64Relop (I64LtEq, e1, e2) -> I64Relop (I64Gt, e1, e2)
	| I64Relop (I64GtEq, e1, e2) -> I64Relop (I64Lt, e1, e2)
	| I64Binop (op, e1, e2) -> 
      begin match op with
		  | I64And -> I64Binop (I64Or, (neg_expr e1), (neg_expr e2))
		  | I64Or -> I64Binop (I64And, (neg_expr e1), (neg_expr e2))
		  | _ -> e
      end
	(* F32 *)
	| F32Relop (F32Eq, e1, e2) -> F32Relop (F32Neq, e1, e2) 
	| F32Relop (F32Neq, e1, e2) -> F32Relop (F32Eq, e1, e2)
	| F32Relop (F32Lt, e1, e2) -> F32Relop (F32GtEq, e1, e2)
	| F32Relop (F32Gt, e1, e2) -> F32Relop (F32LtEq, e1, e2)
	| F32Relop (F32LtEq, e1, e2) -> F32Relop (F32Gt, e1, e2)
	| F32Relop (F32GtEq, e1, e2) -> F32Relop (F32Lt, e1, e2)
	(* F64 *)
	| F64Relop (F64Eq, e1, e2) -> F64Relop (F64Neq, e1, e2) 
	| F64Relop (F64Neq, e1, e2) -> F64Relop (F64Eq, e1, e2)
	| F64Relop (F64Lt, e1, e2) -> F64Relop (F64GtEq, e1, e2)
	| F64Relop (F64Gt, e1, e2) -> F64Relop (F64LtEq, e1, e2)
	| F64Relop (F64LtEq, e1, e2) -> F64Relop (F64Gt, e1, e2)
	| F64Relop (F64GtEq, e1, e2) -> F64Relop (F64Lt, e1, e2)
	(* Value *)
  | Value v ->
      begin match v with
      | I32 0l -> Value (I32 (Int32.of_int 1))
      | I32 _  -> Value (I32 0l)
      | _ -> e
      end
  | BoolOp (And, e1, e2) -> BoolOp (Or , neg_expr e1, neg_expr e2)
  | BoolOp (Or , e1, e2) -> BoolOp (And, neg_expr e1, neg_expr e2)
  | _ -> e
  end

(* Measure complexity of formulas *)
let rec size_expr (e : sym_expr) : int = 
  begin match e with
  | Value v -> 1
	(* I32 *)
	| I32Unop  (op, e)      -> 1 + (size_expr e)
	| I32Binop (op, e1, e2) -> 1 + (size_expr e1) + (size_expr e2)
	| I32Relop (op, e1, e2) -> 1 + (size_expr e1) + (size_expr e2)
	(* I64 *)
	| I64Unop  (op, e)      -> 1 + (size_expr e)
	| I64Binop (op, e1, e2) -> 1 + (size_expr e1) + (size_expr e2)
	| I64Relop (op, e1, e2) -> 1 + (size_expr e1) + (size_expr e2)
	(* F32 *)
	| F32Unop  (op, e)      -> 1 + (size_expr e)
	| F32Binop (op, e1, e2) -> 1 + (size_expr e1) + (size_expr e2)
	| F32Relop (op, e1, e2) -> 1 + (size_expr e1) + (size_expr e2)
	(* F64 *)
	| F64Unop  (op, e)      -> 1 + (size_expr e)
	| F64Binop (op, e1, e2) -> 1 + (size_expr e1) + (size_expr e2)
	| F64Relop (op, e1, e2) -> 1 + (size_expr e1) + (size_expr e2)
  (* Symbol *)
	| Symbolic (s, x)       -> 1
  | Extract  (e, _)       -> 1 + (size_expr e)
  | Concat   (e1, e2)     -> 1 + (size_expr e1) + (size_expr e2)
  | BoolOp   (op, e1, e2) -> 1 + (size_expr e1) + (size_expr e2)
  end

(*  Negates a list of expressions, and ORs them  *)
let rec neg_list (lst : sym_expr list ) : sym_expr =
	begin match lst with 
	| [] ->
			failwith "Trying to negate an empty list"
	| e :: [] -> neg_expr e 
	| e :: es -> BoolOp (Or, (neg_expr e), (neg_list es))
  end

(*  Ands a list of expressions *)
let rec and_list (lst : sym_expr list ) : sym_expr =
	begin match lst with 
  | []      -> failwith "Trying to AND an empty list"
	| e :: [] -> e
	| e :: es -> BoolOp (And, e, (and_list es))
  end

(*  Retrieves the symbolic variables  *)
let rec get_symbols (e : sym_expr) : (string * symbolic) list = 
	begin match e with
  (* Value - holds no symbols *)
	| Value v -> []
  (* I32 *)
  | I32Unop  (op, e1)     -> (get_symbols e1)
  | I32Binop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  | I32Relop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  (* I64 *)
  | I64Unop  (op, e1)     -> (get_symbols e1)
  | I64Binop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  | I64Relop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  (* F32 *)
  | F32Unop  (op, e1)     -> (get_symbols e1)
  | F32Binop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  | F32Relop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  (* F64 *)
  | F64Unop  (op, e1)     -> (get_symbols e1)
  | F64Binop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  | F64Relop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  (* Symbol *)
  | Symbolic (t, x)       -> [(x, t)]
  | Extract  (e, _)       -> (get_symbols e)
  | Concat   (e1, e2)     -> (get_symbols e1) @ (get_symbols e2)
  | BoolOp   (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  end

(*  String representation of an symbolic types  *)
let string_of_symbolic (op : symbolic) : string =
  begin match op with 
	| SymInt32   -> "SymInt32"
	| SymInt64   -> "SymInt64"
	| SymFloat32 -> "SymFloat32"
	| SymFloat64 -> "SymFloat64"
  end

(*  String representation of a sym_expr  *)
let rec to_string (e : sym_expr) : string =
	begin match e with
  | Value v ->
      string_of_value v
	(* I32 *)
  | I32Unop  (op, e) -> 
      let str_e = to_string e in
      let str_op = Si32.string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | I32Binop (op, e1, e2) -> 
      let str_e1 = to_string e1 in
      let str_e2 = to_string e2 in
      let str_op = Si32.string_of_binop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | I32Relop  (op, e1, e2) -> 
      let str_e1 = to_string e1 in
      let str_e2 = to_string e2 in
      let str_op = Si32.string_of_relop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
	(* I64 *)
  | I64Unop  (op, e) ->
      let str_e = to_string e in
      let str_op = Si64.string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | I64Binop (op, e1, e2) ->
      let str_e1 = to_string e1 in
      let str_e2 = to_string e2 in
      let str_op = Si64.string_of_binop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | I64Relop (op, e1, e2) ->
      let str_e1 = to_string e1 in
      let str_e2 = to_string e2 in
      let str_op = Si64.string_of_relop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
	(* F32 *)
  | F32Unop  (op, e) ->
      let str_e = to_string e in
      let str_op = Sf32.string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | F32Binop (op, e1, e2) ->
      let str_e1 = to_string e1 in
      let str_e2 = to_string e2 in
      let str_op = Sf32.string_of_binop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | F32Relop (op, e1, e2) ->
      let str_e1 = to_string e1 in
      let str_e2 = to_string e2 in
      let str_op = Sf32.string_of_relop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  (* F64 *)
  | F64Unop  (op, e) ->
      let str_e = to_string e in
      let str_op = Sf64.string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | F64Binop (op, e1, e2) -> 
      let str_e1 = to_string e1 in
      let str_e2 = to_string e2 in
      let str_op = Sf64.string_of_binop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | F64Relop (op, e1, e2) ->
      let str_e1 = to_string e1 in
      let str_e2 = to_string e2 in
      let str_op = Sf64.string_of_relop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
	(* Symbolic *)
  | Symbolic (s, x) -> 
      let str_s = string_of_symbolic s in
      "(" ^ str_s ^ " #" ^ x ^ ")"
  | Extract (e, i) ->
      let str_e = to_string e in
      "(Extract " ^ str_e ^ ", " ^ (string_of_int i) ^ ")"
  | Concat (e1, e2) ->
      let str_e1 = to_string e1 in
      let str_e2 = to_string e2 in
      "(Concat " ^ str_e1 ^ " " ^ str_e2 ^ ")"
  | BoolOp (op, e1, e2) ->
      let str_e1 = to_string e1 in
      let str_e2 = to_string e2 in
      let str_op =
        match op with
        | And -> "And"
        | Or  -> "Or"
      in
      "(" ^ str_op ^ " " ^ str_e1 ^ " " ^ str_e2 ^ ")"
  end

let rec pp_to_string (e : sym_expr) : string =
	begin match e with
  | Value v -> 
      Values.string_of_value v
  (* I32 *)
  | I32Unop  (op, e) -> 
      let str_e = pp_to_string e in
      let str_op = Si32.pp_string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | I32Binop (op, e1, e2) -> 
      let str_e1 = pp_to_string e1 in
      let str_e2 = pp_to_string e2 in
      let str_op = Si32.pp_string_of_binop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
 | I32Relop (op, e1, e2) -> 
      let str_e1 = pp_to_string e1 in
      let str_e2 = pp_to_string e2 in
      let str_op = Si32.pp_string_of_relop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  (* I64 *)
  | I64Unop  (op, e) ->
      let str_e = pp_to_string e in
      let str_op = Si64.pp_string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | I64Binop (op, e1, e2) ->
      let str_e1 = pp_to_string e1 in
      let str_e2 = pp_to_string e2 in
      let str_op = Si64.pp_string_of_binop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | I64Relop (op, e1, e2) ->
      let str_e1 = pp_to_string e1 in
      let str_e2 = pp_to_string e2 in
      let str_op = Si64.pp_string_of_relop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  (* F32 *)
  | F32Unop  (op, e) ->
      let str_e = pp_to_string e in
      let str_op = Sf32.pp_string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | F32Binop (op, e1, e2) ->
      let str_e1 = pp_to_string e1 in
      let str_e2 = pp_to_string e2 in
      let str_op = Sf32.pp_string_of_binop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | F32Relop (op, e1, e2) ->
      let str_e1 = pp_to_string e1 in
      let str_e2 = pp_to_string e2 in
      let str_op = Sf32.pp_string_of_relop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  (* F64 *)
  | F64Unop  (op, e) ->
      let str_e = pp_to_string e in
      let str_op = Sf64.pp_string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | F64Binop (op, e1, e2) -> 
      let str_e1 = pp_to_string e1 in
      let str_e2 = pp_to_string e2 in
      let str_op = Sf64.pp_string_of_binop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | F64Relop (op, e1, e2) ->
      let str_e1 = pp_to_string e1 in
      let str_e2 = pp_to_string e2 in
      let str_op = Sf64.pp_string_of_relop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | Symbolic (s, x) -> "#" ^ x
  | Extract (e, i) ->
      let str_e = pp_to_string e in
      str_e ^ "[" ^ (string_of_int i) ^ "]"
  | Concat (e1, e2) ->
      let str_e1 = pp_to_string e1 in
      let str_e2 = pp_to_string e2 in
      "(" ^ str_e1 ^ " + " ^ str_e2 ^ ")"
  | BoolOp (op, e1, e2) ->
      let str_e1 = pp_to_string e1 in
      let str_e2 = pp_to_string e2 in
      let str_op =
        match op with
        | And -> "&&"
        | Or  -> "||"
      in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  end

(*  String representation of a list of path conditions  *)
let string_of_pc (pc : path_conditions) : string = 
  List.fold_left (fun acc c -> acc ^ (to_string c) ^ ";  ") "" pc

let pp_string_of_pc (pc : path_conditions) : string = 
  List.fold_left (fun acc e -> acc ^ (pp_to_string e) ^ ";  ") "" pc

let string_of_sym_value (el : sym_value list) : string = 
  List.fold_left (
    fun acc (v, s) -> 
      acc ^ (Values.string_of_value v) ^ ", " ^ (pp_to_string s) ^ "\n"
  ) "" el

let rec simplify (e : sym_expr) : sym_expr =
  begin match e with
  | Value v -> Value v
  | I32Binop (I32Add, ex1, ex2) ->
      let ex1' = simplify ex1 in
      let ex2' = simplify ex2 in
      begin match ex1', ex2' with
      | Value v1, Value v2 -> Value (Eval_numeric.eval_binop (I32 Ast.I32Op.Add) v1 v2)
      | _ -> I32Binop (I32Add, ex1', ex2')
      end
  | I32Binop (I32Shl, ex1, ex2) ->
      let ex1' = simplify ex1 in
      let ex2' = simplify ex2 in
      begin match ex2' with
      | Value (Values.I32 v) ->
          let power = int_of_float (2. ** (float_of_int (Int32.to_int v))) in
          I32Binop (I32Mul, ex1', Value (I32 (Int32.of_int power)))
      | _ -> I32Binop (I32Shl, ex1', ex2')
      end
  | I32Binop (I32ShrS, ex1, ex2) ->
      let ex1' = simplify ex1 in
      let ex2' = simplify ex2 in
      begin match ex2' with
      | Value (Values.I32 v) ->
          let power = int_of_float (2. ** (float_of_int (Int32.to_int v))) in
          I32Binop (I32DivS, ex1', Value (I32 (Int32.of_int power)))
      | _ -> I32Binop (I32Shl, ex1', ex2')
      end

  | I32Relop (I32Eq, ex1, ex2) ->
      let ex1' = simplify ex1 in
      let ex2' = simplify ex2 in
      begin match ex1', ex2' with
       | Value  v1, Value  v2 -> Value (I32 (if (Eval_numeric.eval_relop (I32 Ast.I32Op.Eq) v1 v2) then (Int32.of_int 1) else 0l))
       | _ -> I32Relop (I32Eq, ex1', ex2')
      end
  | _ -> e
  end
