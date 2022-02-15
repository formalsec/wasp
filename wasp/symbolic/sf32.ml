type binop = F32Add | F32Sub | F32Mul | F32Div | F32Min | F32Max (*  Falta: | CopySign *)
type unop  = F32Neg | F32Abs | F32Sqrt (*  Falta: | Ceil | Floor | Trunc | Nearest *)
type relop = F32Eq | F32Ne | F32Lt |  F32Le | F32Gt | F32Ge
type cvtop = F32DemoteF64 | F32ConvertSI32 | F32ConvertUI32 |
             F32ConvertSI64 | F32ConvertUI64 | F32ReinterpretInt

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
	| F32Min -> "F32Min"
	| F32Max -> "F32Max"

let pp_string_of_binop (op : binop) : string =
	match op with
	| F32Add -> "+"
	| F32Sub -> "-"
	| F32Mul -> "*"
	| F32Div -> "/"
	| F32Min -> "F32Min"
	| F32Max -> "F32Max"

(*  String representation of an f32 unary operation  *)
let string_of_unop (op : unop) : string =
	match op with
	| F32Neg -> "F32Neg"
  | F32Abs -> "F32Abs"
  | F32Sqrt -> "F32Sqrt"

let pp_string_of_unop (op : unop) : string =
	match op with
	| F32Neg -> "-"
  | F32Abs -> "F32Abs"
  | F32Sqrt -> "F32Sqrt"

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

let string_of_cvtop (op : cvtop) : string =
  match op with
  | F32DemoteF64 -> "F32DemoteF64"
  | F32ConvertSI32 -> "F32ConvertSI32"
  | F32ConvertUI32 -> "F32ConvertUI32"
  | F32ConvertSI64 -> "F32ConvertSI64"
  | F32ConvertUI64 -> "F32ConvertUI64"
  | F32ReinterpretInt -> "F32ReinterpretInt"

let pp_string_of_cvtop (op : cvtop) : string =
  string_of_cvtop op
