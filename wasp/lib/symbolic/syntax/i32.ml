type binop =
  | I32Add
  | I32Mul
  | I32DivU
  | I32RemU
  | I32ShrU
  | I32And
  | I32Sub
  | I32Shl
  | I32DivS
  | I32RemS
  | I32ShrS
  | I32Or
  | I32Xor

type unop = I32Clz (*  Falta:  Ctz | Popcnt *)

type relop =
  | I32Eq
  | I32LtU
  | I32LtS
  | I32LeU
  | I32LeS
  | I32Ne
  | I32GtU
  | I32GtS
  | I32GeU
  | I32GeS

type cvtop =
  | I32TruncSF32
  | I32TruncUF32
  | I32TruncSF64
  | I32TruncUF64
  | I32ReinterpretFloat

let neg_relop (op : relop) : relop =
  match op with
  | I32Eq -> I32Ne
  | I32Ne -> I32Eq
  | I32LtU -> I32GeU
  | I32LtS -> I32GeS
  | I32GtU -> I32LeU
  | I32GtS -> I32LeS
  | I32LeU -> I32GtU
  | I32LeS -> I32GtS
  | I32GeU -> I32LtU
  | I32GeS -> I32LtS

(*  String representation of an i32 binary operation  *)
let string_of_binop (op : binop) : string =
  match op with
  | I32Add -> "I32Add"
  | I32And -> "I32And"
  | I32Or -> "I32Or"
  | I32Sub -> "I32Sub"
  | I32DivS -> "I32DivS"
  | I32DivU -> "I32DivU"
  | I32Xor -> "I32Xor"
  | I32Mul -> "I32Mul"
  | I32Shl -> "I32Shl"
  | I32ShrS -> "I32ShrS"
  | I32ShrU -> "I32ShrU"
  | I32RemS -> "I32RemS"
  | I32RemU -> "I32RemU"

let pp_string_of_binop (op : binop) : string =
  match op with
  | I32Add -> "+"
  | I32And -> "&"
  | I32Or -> "|"
  | I32Sub -> "-"
  | I32DivS -> "/"
  | I32DivU -> "/u"
  | I32Xor -> "^"
  | I32Mul -> "*"
  | I32Shl -> "<<"
  | I32ShrS -> ">>"
  | I32ShrU -> ">>u"
  | I32RemS -> "%"
  | I32RemU -> "%u"

(*  String representation of an i32 unary operation  *)
let string_of_unop (op : unop) : string = match op with I32Clz -> "I32Clz"
let pp_string_of_unop (op : unop) : string = match op with I32Clz -> "Clz"

(*  String representation of an i32 relative operation  *)
let string_of_relop (op : relop) : string =
  match op with
  | I32Eq -> "I32Eq"
  | I32Ne -> "I32Ne"
  | I32LtU -> "I32LtU"
  | I32LtS -> "I32LtS"
  | I32GtU -> "I32GtU"
  | I32GtS -> "I32GtS"
  | I32LeU -> "I32LeU"
  | I32LeS -> "I32LeS"
  | I32GeU -> "I32GeU"
  | I32GeS -> "I32GeS"

let pp_string_of_relop (op : relop) : string =
  match op with
  | I32Eq -> "=="
  | I32Ne -> "!="
  | I32LtU -> "<"
  | I32LtS -> "<"
  | I32GtU -> ">"
  | I32GtS -> ">"
  | I32LeU -> "<="
  | I32LeS -> "<="
  | I32GeU -> ">="
  | I32GeS -> ">="

let string_of_cvtop (op : cvtop) : string =
  match op with
  | I32TruncSF32 -> "I32TruncSF32"
  | I32TruncUF32 -> "I32TruncUF32"
  | I32TruncSF64 -> "I32TruncSF64"
  | I32TruncUF64 -> "I32TruncUF64"
  | I32ReinterpretFloat -> "I32ReinterpretFloat"

let pp_string_of_cvtop (op : cvtop) : string = string_of_cvtop op
