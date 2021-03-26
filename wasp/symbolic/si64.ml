type binop = I64Add | I64Mul | I64And | (*  Falta: | Shl | ShrS | ShrU | Rotl | Rotr  *)
             I64Sub | I64Div | I64Or  | I64Xor 
type unop  = I64Clz (*  Falta: | Clz | Ctz | Popcnt *)
type relop = I64Eq | I64LtU | I64LtS | I64LeU | I64LeS |
             I64Ne | I64GtU | I64GtS | I64GeU | I64GeS

let neg_relop (op : relop) : relop =
  begin match op with
  | I64Eq  -> I64Ne
  | I64Ne  -> I64Eq
  | I64LtU -> I64GeU
  | I64LtS -> I64GeS
  | I64GtU -> I64LeU
  | I64GtS -> I64LeS
  | I64LeU -> I64GtU
  | I64LeS -> I64GtS
  | I64GeU -> I64LtU
  | I64GeS -> I64LtS
  end

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
	| I64And  -> "&"
	| I64Or   -> "|"
	| I64Sub  -> "-"
	| I64Div  -> "/"
	| I64Xor  -> "^"
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
	| I64Eq  -> "I64Eq"
	| I64Ne  -> "I64Ne"
	| I64LtU -> "I64LtU"
	| I64LtS -> "I64LtS"
	| I64GtU -> "I64GtU"
	| I64GtS -> "I64GtS"
	| I64LeU -> "I64LeU"
	| I64LeS -> "I64LeS"
	| I64GeU -> "I64GeU"
	| I64GeS -> "I64GeS"

let pp_string_of_relop (op : relop) : string =
	match op with 
	| I64Eq  -> "=="
	| I64Ne  -> "!="
	| I64LtU -> "<"
	| I64LtS -> "<"
	| I64GtU -> ">"
	| I64GtS -> ">"
	| I64LeU -> "<="
	| I64LeS -> "<="
	| I64GeU -> ">="
	| I64GeS -> ">="
