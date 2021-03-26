type binop = F64Add | F64Sub | F64Mul | F64Div (*  Falta: | Min | Max | CopySign *)
type unop  = F64Neg (*  Falta: | Abs | Ceil | Floor | Trunc | Nearest | Sqrt *)
type relop = F64Eq | F64Ne | F64Lt | F64Le | F64Gt | F64Ge

let neg_relop (op : relop) : relop =
  begin match op with
  | F64Eq -> F64Ne
  | F64Ne -> F64Eq
  | F64Lt -> F64Ge
  | F64Gt -> F64Le
  | F64Le -> F64Gt
  | F64Ge -> F64Lt
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
	| F64Eq -> "F64Eq"
	| F64Ne -> "F64Ne"
	| F64Lt -> "F64Lt"
	| F64Gt -> "F64Gt"
	| F64Le -> "F64Le"
	| F64Ge -> "F64Ge"

let pp_string_of_relop (op : relop) : string =
	match op with 
	| F64Eq -> "=="
	| F64Ne -> "!="
	| F64Lt -> "<"
	| F64Gt -> ">"
	| F64Le -> "<="
	| F64Ge -> ">="
