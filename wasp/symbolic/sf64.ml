type binop = F64Add | F64Sub | F64Mul | F64Div (*  Falta: | Min | Max | CopySign *)
type unop  = F64Neg (*  Falta: | Abs | Ceil | Floor | Trunc | Nearest | Sqrt *)
type relop = F64Eq | F64Neq | F64Lt | F64LtEq | F64Gt | F64GtEq (*  All done  *)

let neg_relop (op : relop) : relop =
  begin match op with
  | F64Eq   -> F64Neq
  | F64Neq  -> F64Eq
  | F64Lt   -> F64GtEq
  | F64Gt   -> F64LtEq
  | F64LtEq -> F64Gt
  | F64GtEq -> F64Lt
  end

(*  String representation of an f64 binary operation  *)
let string_of_binop (op : binop) : string =
	match op with
	| F64Add -> "F64Add"
	| F64Sub -> "F64Sub"
	| F64Mul -> "F64Mul"
	| F64Div -> "F64Div"

let pp_string_of_binop (op : binop) : string =
	match op with
	| F64Add -> "+"
	| F64Sub -> "-"
	| F64Mul -> "*"
	| F64Div -> "/"

(*  String representation of an f64 unary operation  *)
let string_of_unop (op : unop) : string =
	match op with 
	| F64Neg -> "F64Neg"

let pp_string_of_unop (op : unop) : string =
	match op with 
	| F64Neg -> "-"

(*  String representation of an f64 relative operation  *)
let string_of_relop (op : relop) : string =
	match op with 
	| F64Eq   -> "F64Eq"
	| F64Neq  -> "F64Neq"
	| F64Lt   -> "F64Lt"
	| F64Gt   -> "F64Gt"
	| F64LtEq -> "F64LtEq"
	| F64GtEq -> "F64GtEq"

let pp_string_of_relop (op : relop) : string =
	match op with 
	| F64Eq   -> "=="
	| F64Neq  -> "!="
	| F64Lt   -> "<"
	| F64Gt   -> ">"
	| F64LtEq -> "<="
	| F64GtEq -> ">="
