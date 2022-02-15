type binop = F64Add | F64Sub | F64Mul | F64Div (*  Falta: | Min | Max | CopySign *)
type unop  = F64Neg | F64Abs (*  Falta: Ceil | Floor | Trunc | Nearest | Sqrt *)
type relop = F64Eq | F64Ne | F64Lt | F64Le | F64Gt | F64Ge
type cvtop = F64PromoteF32 | F64ConvertSI32 | F64ConvertUI32 |
             F64ConvertSI64 | F64ConvertUI64 | F64ReinterpretInt

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
	| F64Abs -> "F64Abs"

let pp_string_of_unop (op : unop) : string =
	match op with
	| F64Neg -> "-"
	| F64Abs -> "F64Abs"

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

let string_of_cvtop (op : cvtop) : string =
  match op with
  | F64PromoteF32 -> "F64PromoteF32"
  | F64ConvertSI32 -> "F64ConvertSI32"
  | F64ConvertUI32 -> "F64ConvertUI32"
  | F64ConvertSI64 -> "F64ConvertSI64"
  | F64ConvertUI64 -> "F64ConvertUI64"
  | F64ReinterpretInt -> "F64ReinterpretInt"

let pp_string_of_cvtop (op : cvtop) : string =
  string_of_cvtop op
