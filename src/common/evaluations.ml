open Smtml
open Expr
open Ty
open Interpreter.Ast

exception Unsupported_op of string

let to_value (n : Num.t) : Interpreter.Values.value =
  let open Interpreter in
  match n with
  | Num.I32 i -> Values.I32 i
  | Num.I64 i -> Values.I64 i
  | Num.F32 f -> Values.F32 (F32.of_bits f)
  | Num.F64 f -> Values.F64 (F64.of_bits f)
  | Num.I8 _ -> assert false

let of_value (v : Interpreter.Values.value) : Num.t =
  let open Interpreter in
  match v with
  | Values.I32 i -> Num.I32 i
  | Values.I64 i -> Num.I64 i
  | Values.F32 f -> Num.F32 (F32.to_bits f)
  | Values.F64 f -> Num.F64 (F64.to_bits f)

let ty_of_num_type (t : Interpreter.Types.value_type) =
  let open Interpreter in
  match t with
  | Types.I32Type -> Ty_bitv 32
  | Types.I64Type -> Ty_bitv 64
  | Types.F32Type -> Ty_fp 32
  | Types.F64Type -> Ty_fp 64

let f32_unop op e =
  match op with
  | F32Op.Neg -> unop (Ty_fp 32) Neg e
  | F32Op.Abs -> unop (Ty_fp 32) Abs e
  | F32Op.Sqrt -> unop (Ty_fp 32) Sqrt e
  | F32Op.Nearest -> unop (Ty_fp 32) Nearest e
  | F32Op.Ceil -> unop (Ty_fp 32) Ceil e
  | F32Op.Floor -> unop (Ty_fp 32) Floor e
  | F32Op.Trunc -> unop (Ty_fp 32) Trunc e

let f64_unop op e =
  match op with
  | F64Op.Neg -> unop (Ty_fp 64) Neg e
  | F64Op.Abs -> unop (Ty_fp 64) Abs e
  | F64Op.Sqrt -> unop (Ty_fp 64) Sqrt e
  | F64Op.Nearest -> unop (Ty_fp 64) Nearest e
  | F64Op.Ceil -> unop (Ty_fp 64) Ceil e
  | F64Op.Floor -> unop (Ty_fp 64) Floor e
  | F64Op.Trunc -> unop (Ty_fp 64) Trunc e

let i32_binop op e1 e2 =
  match op with
  | I32Op.Add -> binop (Ty_bitv 32) Add e1 e2
  | I32Op.And -> binop (Ty_bitv 32) And e1 e2
  | I32Op.Or -> binop (Ty_bitv 32) Or e1 e2
  | I32Op.Sub -> binop (Ty_bitv 32) Sub e1 e2
  | I32Op.DivS -> binop (Ty_bitv 32) Div e1 e2
  | I32Op.DivU -> binop (Ty_bitv 32) DivU e1 e2
  | I32Op.Xor -> binop (Ty_bitv 32) Xor e1 e2
  | I32Op.Mul -> binop (Ty_bitv 32) Mul e1 e2
  | I32Op.Shl -> binop (Ty_bitv 32) Shl e1 e2
  | I32Op.ShrS -> binop (Ty_bitv 32) ShrA e1 e2
  | I32Op.ShrU -> binop (Ty_bitv 32) ShrL e1 e2
  | I32Op.RemS -> binop (Ty_bitv 32) Rem e1 e2
  | I32Op.RemU -> binop (Ty_bitv 32) RemU e1 e2
  | I32Op.Rotl -> binop (Ty_bitv 32) Rotl e1 e2
  | I32Op.Rotr -> binop (Ty_bitv 32) Rotr e1 e2

let i64_binop op e1 e2 =
  match op with
  | I64Op.Add -> binop (Ty_bitv 64) Add e1 e2
  | I64Op.And -> binop (Ty_bitv 64) And e1 e2
  | I64Op.Or -> binop (Ty_bitv 64) Or e1 e2
  | I64Op.Sub -> binop (Ty_bitv 64) Sub e1 e2
  | I64Op.DivS -> binop (Ty_bitv 64) Div e1 e2
  | I64Op.DivU -> binop (Ty_bitv 64) DivU e1 e2
  | I64Op.Xor -> binop (Ty_bitv 64) Xor e1 e2
  | I64Op.Mul -> binop (Ty_bitv 64) Mul e1 e2
  | I64Op.Shl -> binop (Ty_bitv 64) Shl e1 e2
  | I64Op.ShrS -> binop (Ty_bitv 64) ShrA e1 e2
  | I64Op.ShrU -> binop (Ty_bitv 64) ShrL e1 e2
  | I64Op.RemS -> binop (Ty_bitv 64) Rem e1 e2
  | I64Op.RemU -> binop (Ty_bitv 64) RemU e1 e2
  | I64Op.Rotl -> binop (Ty_bitv 64) Rotl e1 e2
  | I64Op.Rotr -> binop (Ty_bitv 64) Rotr e1 e2

let f32_binop op e1 e2 =
  match op with
  | F32Op.Add -> binop (Ty_fp 32) Add e1 e2
  | F32Op.Sub -> binop (Ty_fp 32) Sub e1 e2
  | F32Op.Div -> binop (Ty_fp 32) Div e1 e2
  | F32Op.Mul -> binop (Ty_fp 32) Mul e1 e2
  | F32Op.Min -> binop (Ty_fp 32) Min e1 e2
  | F32Op.Max -> binop (Ty_fp 32) Max e1 e2
  | F32Op.CopySign -> failwith "eval F32Binop: TODO CopySign"

let f64_binop op e1 e2 =
  match op with
  | F64Op.Add -> binop (Ty_fp 64) Add e1 e2
  | F64Op.Sub -> binop (Ty_fp 64) Sub e1 e2
  | F64Op.Div -> binop (Ty_fp 64) Div e1 e2
  | F64Op.Mul -> binop (Ty_fp 64) Mul e1 e2
  | F64Op.Min -> binop (Ty_fp 64) Min e1 e2
  | F64Op.Max -> binop (Ty_fp 64) Max e1 e2
  | F64Op.CopySign -> failwith "eval F64Binop: TODO CopySign"

let i32_relop op e1 e2 =
  match op with
  | I32Op.Eq -> relop Ty_bool Eq e1 e2
  | I32Op.Ne -> relop Ty_bool Ne e1 e2
  | I32Op.LtU -> relop (Ty_bitv 32) LtU e1 e2
  | I32Op.LtS -> relop (Ty_bitv 32) Lt e1 e2
  | I32Op.GtU -> relop (Ty_bitv 32) GtU e1 e2
  | I32Op.GtS -> relop (Ty_bitv 32) Gt e1 e2
  | I32Op.LeU -> relop (Ty_bitv 32) LeU e1 e2
  | I32Op.LeS -> relop (Ty_bitv 32) Le e1 e2
  | I32Op.GeU -> relop (Ty_bitv 32) GeU e1 e2
  | I32Op.GeS -> relop (Ty_bitv 32) Ge e1 e2

let i64_relop op e1 e2 =
  match op with
  | I64Op.Eq -> relop Ty_bool Eq e1 e2
  | I64Op.Ne -> relop Ty_bool Ne e1 e2
  | I64Op.LtU -> relop (Ty_bitv 64) LtU e1 e2
  | I64Op.LtS -> relop (Ty_bitv 64) Lt e1 e2
  | I64Op.GtU -> relop (Ty_bitv 64) GtU e1 e2
  | I64Op.GtS -> relop (Ty_bitv 64) Gt e1 e2
  | I64Op.LeU -> relop (Ty_bitv 64) LeU e1 e2
  | I64Op.LeS -> relop (Ty_bitv 64) Le e1 e2
  | I64Op.GeU -> relop (Ty_bitv 64) GeU e1 e2
  | I64Op.GeS -> relop (Ty_bitv 64) Ge e1 e2

let f32_relop op e1 e2 =
  match op with
  | F32Op.Eq -> relop (Ty_fp 32) Eq e1 e2
  | F32Op.Ne -> relop (Ty_fp 32) Ne e1 e2
  | F32Op.Lt -> relop (Ty_fp 32) Lt e1 e2
  | F32Op.Gt -> relop (Ty_fp 32) Gt e1 e2
  | F32Op.Le -> relop (Ty_fp 32) Le e1 e2
  | F32Op.Ge -> relop (Ty_fp 32) Ge e1 e2

let f64_relop op e1 e2 =
  match op with
  | F64Op.Eq -> relop (Ty_fp 64) Eq e1 e2
  | F64Op.Ne -> relop (Ty_fp 64) Ne e1 e2
  | F64Op.Lt -> relop (Ty_fp 64) Lt e1 e2
  | F64Op.Gt -> relop (Ty_fp 64) Gt e1 e2
  | F64Op.Le -> relop (Ty_fp 64) Le e1 e2
  | F64Op.Ge -> relop (Ty_fp 64) Ge e1 e2

(* TODO: sign bit *)
let i32_cvtop op s =
  match op with
  (* 64bit integer is taken modulo 2^32 i.e., top 32 bits are lost *)
  | I32Op.WrapI64 -> extract s ~high:4 ~low:0
  | I32Op.TruncSF32 -> cvtop (Ty_bitv 32) TruncSF32 s
  | I32Op.TruncUF32 -> cvtop (Ty_bitv 32) TruncUF32 s
  | I32Op.TruncSF64 -> cvtop (Ty_bitv 32) TruncSF64 s
  | I32Op.TruncUF64 -> cvtop (Ty_bitv 32) TruncUF64 s
  | I32Op.ReinterpretFloat -> cvtop (Ty_bitv 32) Reinterpret_float s
  | I32Op.ExtendSI32 -> failwith "TypeError"
  | I32Op.ExtendUI32 -> failwith "TypeError"

let i64_cvtop op s =
  match op with
  | I64Op.ExtendSI32 -> cvtop (Ty_bitv 64) (Sign_extend 32)  s
  | I64Op.ExtendUI32 -> cvtop (Ty_bitv 64) (Zero_extend 32) s
  | I64Op.TruncSF32 -> cvtop (Ty_bitv 64) TruncSF32 s
  | I64Op.TruncUF32 -> cvtop (Ty_bitv 64) TruncUF32 s
  | I64Op.TruncSF64 -> cvtop (Ty_bitv 64) TruncSF64 s
  | I64Op.TruncUF64 -> cvtop (Ty_bitv 64) TruncUF64 s
  | I64Op.ReinterpretFloat -> cvtop (Ty_bitv 64) Reinterpret_float s
  | I64Op.WrapI64 -> failwith "TypeError"

let f32_cvtop op s =
  match op with
  | F32Op.DemoteF64 -> cvtop (Ty_fp 32) DemoteF64 s
  | F32Op.ConvertSI32 -> cvtop (Ty_fp 32) ConvertSI32 s
  | F32Op.ConvertUI32 -> cvtop (Ty_fp 32) ConvertUI32 s
  | F32Op.ConvertSI64 -> cvtop (Ty_fp 32) ConvertSI64 s
  | F32Op.ConvertUI64 -> cvtop (Ty_fp 32) ConvertUI64 s
  | F32Op.ReinterpretInt -> cvtop (Ty_fp 32) Reinterpret_int s
  | F32Op.PromoteF32 -> failwith "TypeError"

let f64_cvtop op s =
  match op with
  | F64Op.PromoteF32 -> cvtop (Ty_fp 64) PromoteF32 s
  | F64Op.ConvertSI32 -> cvtop (Ty_fp 64) ConvertSI32 s
  | F64Op.ConvertUI32 -> cvtop (Ty_fp 64) ConvertUI32 s
  | F64Op.ConvertSI64 -> cvtop (Ty_fp 64) ConvertSI64 s
  | F64Op.ConvertUI64 -> cvtop (Ty_fp 64) ConvertUI64 s
  | F64Op.ReinterpretInt -> cvtop (Ty_fp 64) Reinterpret_int s
  | F64Op.DemoteF64 -> failwith "TypeError"
