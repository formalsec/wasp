type binop = I32Add | I32And | I32Or | I32Sub | I32Mul | I32DivS | I32DivU | I32Xor | I32Shl | I32ShrS | I32ShrU (*  Falta:  Rotl | Rotr  *)
type unop  = I32Clz (*  Falta: | Clz | Ctz | Popcnt *)
type relop = I32Eq | I32Neq | I32Lt | I32LtEq | I32Gt | I32GtEq (*  All done, except Unsigned operations  *)

(*  String representation of an i32 binary operation  *)
let string_of_binop (op : binop) : string =
	match op with
	| I32Add  -> "I32Add"
	| I32And  -> "I32And"
	| I32Or   -> "I32Or"
	| I32Sub  -> "I32Sub"
	| I32DivS -> "I32DivS"
  | I32DivU -> "I32DivU"
	| I32Xor  -> "I32Xor"
	| I32Mul  -> "I32Mul"
  | I32Shl  -> "I32Shl"
  | I32ShrS -> "I32ShrS"
  | I32ShrU -> "I32ShrU"

let pp_string_of_binop (op : binop) : string =
	match op with
	| I32Add  -> "+"
	| I32And  -> "/\\"
	| I32Or   -> "\\/"
	| I32Sub  -> "-"
	| I32DivS -> "/"
	| I32DivU -> "/"
	| I32Xor  -> "Xor"
	| I32Mul  -> "*"
  | I32Shl  -> "<<"
  | I32ShrS -> "s>>"
  | I32ShrU -> "u>>"

(*  String representation of an i32 unary operation  *)
let string_of_unop (op : unop) : string =
	match op with 
	| I32Clz  -> "I32Clz"

let pp_string_of_unop (op : unop) : string =
	match op with 
	| I32Clz  -> "Clz"

(*  String representation of an i32 relative operation  *)
let string_of_relop (op : relop) : string =
	match op with 
	| I32Eq   -> "I32Eq"
	| I32Neq  -> "I32Neq"
	| I32Lt   -> "I32Lt"
	| I32Gt   -> "I32Gt"
	| I32LtEq -> "I32LtEq"
	| I32GtEq -> "I32GtEq"

let pp_string_of_relop (op : relop) : string =
	match op with 
	| I32Eq   -> "=="
	| I32Neq  -> "!="
	| I32Lt   -> "<"
	| I32Gt   -> ">"
	| I32LtEq -> "<="
	| I32GtEq -> ">="
