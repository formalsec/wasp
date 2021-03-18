type binop = I64Add | I64And | I64Or | I64Sub | I64Mul | I64Div | I64Xor (*  Falta: | Shl | ShrS | ShrU | Rotl | Rotr  *)
type unop  = I64Clz (*  Falta: | Clz | Ctz | Popcnt *)
type relop = I64Eq | I64Neq | I64Lt | I64LtEq | I64Gt | I64GtEq (*  All done, except Unsigned operations  *)

(*  String representation of an i64 binary operation  *)
let string_of_binop (op : binop) : string =
	match op with
  | I64Add  -> "I64Add"
	| I64And  -> "I64And"
	| I64Or   -> "I64Or"
	| I64Sub  -> "I64Sub"
	| I64Div  -> "I64Div"
	| I64Xor  -> "I64Xor"
	| I64Mul  -> "I64Mul"

let pp_string_of_binop (op : binop) : string =
	match op with
	| I64Add  -> "+"
	| I64And  -> "/\\"
	| I64Or   -> "\\/"
	| I64Sub  -> "-"
	| I64Div  -> "/"
	| I64Xor  -> "Xor"
	| I64Mul  -> "*"

(*  String representation of an i64 unary operation  *)
let string_of_unop (op : unop) : string =
	match op with 
	| I64Clz  -> "I64Clz"

let pp_string_of_unop (op : unop) : string =
	match op with 
	| I64Clz  -> "Clz"

(*  String representation of an i64 relative operation  *)
let string_of_relop (op : relop) : string =
	match op with 
	| I64Eq   -> "I64Eq"
	| I64Neq  -> "I64Neq"
	| I64Lt   -> "I64Lt"
	| I64Gt   -> "I64Gt"
	| I64LtEq -> "I64LtEq"
	| I64GtEq -> "I64GtEq"

let pp_string_of_relop (op : relop) : string =
	match op with 
	| I64Eq   -> "=="
	| I64Neq  -> "!="
	| I64Lt   -> "<"
	| I64Gt   -> ">"
	| I64LtEq -> "<="
	| I64GtEq -> ">="
