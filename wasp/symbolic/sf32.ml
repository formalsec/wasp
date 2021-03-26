type binop = F32Add | F32Sub | F32Mul | F32Div (*  Falta: | Min | Max | CopySign *)
type unop  = F32Neg (*  Falta: | Abs | Ceil | Floor | Trunc | Nearest | Sqrt *)
type relop = F32Eq | F32Ne | F32Lt |  F32Le | F32Gt | F32Ge

let neg_relop (op : relop) : relop =
  begin match op with
  | F32Eq -> F32Ne
  | F32Ne -> F32Eq
  | F32Lt -> F32Ge
  | F32Gt -> F32Le
  | F32Le -> F32Gt
  | F32Ge -> F32Lt
  end

(*  String representation of an f32 binary operation  *)
let string_of_binop (op : binop) : string =
	match op with
	| F32Add -> "F32Add"
	| F32Sub -> "F32Sub"
	| F32Mul -> "F32Mul"
	| F32Div -> "F32Div"

let pp_string_of_binop (op : binop) : string =
	match op with
	| F32Add -> "+"
	| F32Sub -> "-"
	| F32Mul -> "*"
	| F32Div -> "/"

(*  String representation of an f32 unary operation  *)
let string_of_unop (op : unop) : string =
	match op with 
	| F32Neg -> "F32Neg"

let pp_string_of_unop (op : unop) : string =
	match op with 
	| F32Neg -> "-"

(*  String representation of an f32 relative operation  *)
let string_of_relop (op : relop) : string =
	match op with 
	| F32Eq -> "F32Eq"
	| F32Ne -> "F32Ne"
	| F32Lt -> "F32Lt"
	| F32Gt -> "F32Gt"
	| F32Le -> "F32Le"
	| F32Ge -> "F32Ge"

let pp_string_of_relop (op : relop) : string =
	match op with 
	| F32Eq -> "=="
	| F32Ne -> "!="
	| F32Lt -> "<"
	| F32Gt -> ">"
	| F32Le -> "<="
	| F32Ge -> ">="
