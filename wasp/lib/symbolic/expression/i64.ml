type binop =
  | I64Add
  | I64Mul
  | I64DivU
  | I64RemU
  | I64ShrU
  | I64And
  | I64Sub
  | I64Shl
  | I64DivS
  | I64RemS
  | I64ShrS
  | I64Or
  | I64Xor

type unop = I64Clz (*  Falta: | Ctz | Popcnt *)

type relop =
  | I64Eq
  | I64LtU
  | I64LtS
  | I64LeU
  | I64LeS
  | I64Ne
  | I64GtU
  | I64GtS
  | I64GeU
  | I64GeS

type cvtop =
  | I64ExtendSI32
  | I64ExtendUI32
  | I64TruncSF32
  | I64TruncUF32
  | I64TruncSF64
  | I64TruncUF64
  | I64ReinterpretFloat

let neg_relop (op : relop) : relop =
  match op with
  | I64Eq -> I64Ne
  | I64Ne -> I64Eq
  | I64LtU -> I64GeU
  | I64LtS -> I64GeS
  | I64GtU -> I64LeU
  | I64GtS -> I64LeS
  | I64LeU -> I64GtU
  | I64LeS -> I64GtS
  | I64GeU -> I64LtU
  | I64GeS -> I64LtS

(*  String representation of an i64 binary operation  *)
let string_of_binop (op : binop) : string =
  match op with
  | I64Add -> "I64Add"
  | I64And -> "I64And"
  | I64Or -> "I64Or"
  | I64Sub -> "I64Sub"
  | I64DivS -> "I64DivS"
  | I64DivU -> "I64DivU"
  | I64Xor -> "I64Xor"
  | I64Mul -> "I64Mul"
  | I64Shl -> "I64Shl"
  | I64ShrS -> "I64ShrS"
  | I64ShrU -> "I64ShrU"
  | I64RemS -> "I64RemS"
  | I64RemU -> "I64RemU"

let pp_string_of_binop (op : binop) : string =
  match op with
  | I64Add -> "+"
  | I64And -> "&"
  | I64Or -> "|"
  | I64Sub -> "-"
  | I64DivS -> "/"
  | I64DivU -> "/u"
  | I64Xor -> "^"
  | I64Mul -> "*"
  | I64Shl -> "<<"
  | I64ShrS -> ">>"
  | I64ShrU -> ">>u"
  | I64RemS -> "%"
  | I64RemU -> "%u"

(*  String representation of an i64 unary operation  *)
let string_of_unop (op : unop) : string = match op with I64Clz -> "I64Clz"
let pp_string_of_unop (op : unop) : string = match op with I64Clz -> "Clz"

(*  String representation of an i64 relative operation  *)
let string_of_relop (op : relop) : string =
  match op with
  | I64Eq -> "I64Eq"
  | I64Ne -> "I64Ne"
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
  | I64Eq -> "=="
  | I64Ne -> "!="
  | I64LtU -> "<"
  | I64LtS -> "<"
  | I64GtU -> ">"
  | I64GtS -> ">"
  | I64LeU -> "<="
  | I64LeS -> "<="
  | I64GeU -> ">="
  | I64GeS -> ">="

let string_of_cvtop (op : cvtop) : string =
  match op with
  | I64ExtendSI32 -> "I64ExtendSI32"
  | I64ExtendUI32 -> "I64ExtendUI32"
  | I64TruncSF32 -> "I64TruncSF32"
  | I64TruncUF32 -> "I64TruncUF32"
  | I64TruncSF64 -> "I64TruncSF64"
  | I64TruncUF64 -> "I64TruncUF64"
  | I64ReinterpretFloat -> "I64ReinterpretFloat"

let pp_string_of_cvtop (op : cvtop) : string = string_of_cvtop op
