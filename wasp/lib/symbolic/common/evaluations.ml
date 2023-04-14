open Encoding
open Expression
open Types
open I64
open F64
open Interpreter.Ast

exception UnsupportedOp of string

let to_value (n : Num.t) : Interpreter.Values.value =
  let open Interpreter in
  match n with
  | I32 i -> Values.I32 i
  | I64 i -> Values.I64 i
  | F32 f -> Values.F32 (F32.of_bits f)
  | F64 f -> Values.F64 (F64.of_bits f)

let of_value (v : Interpreter.Values.value) : Num.t =
  let open Interpreter in
  match v with
  | Values.I32 i -> I32 i
  | Values.I64 i -> I64 i
  | Values.F32 f -> F32 (F32.to_bits f)
  | Values.F64 f -> F64 (F64.to_bits f)

let to_num_type (t : Interpreter.Types.value_type) =
  let open Interpreter in
  match t with
  | Types.I32Type -> `I32Type
  | Types.I64Type -> `I64Type
  | Types.F32Type -> `F32Type
  | Types.F64Type -> `F64Type

let f32_unop op e =
  match op with
  | F32Op.Neg -> FloatingPoint.mk_neg e `F32Type
  | F32Op.Abs -> FloatingPoint.mk_abs e `F32Type
  | F32Op.Sqrt -> FloatingPoint.mk_sqrt e `F32Type
  | F32Op.Nearest -> FloatingPoint.mk_nearest e `F32Type
  | F32Op.Ceil -> raise (UnsupportedOp "eval_unop: Ceil")
  | F32Op.Floor -> raise (UnsupportedOp "eval_unop: Floor")
  | F32Op.Trunc -> raise (UnsupportedOp "eval_unop: Trunc")

let f64_unop op e =
  match op with
  | F64Op.Neg -> FloatingPoint.mk_neg e `F64Type
  | F64Op.Abs -> FloatingPoint.mk_abs e `F64Type
  | F64Op.Sqrt -> FloatingPoint.mk_sqrt e `F64Type
  | F64Op.Nearest -> FloatingPoint.mk_nearest e `F64Type
  | F64Op.Ceil -> raise (UnsupportedOp "eval_unop: Ceil")
  | F64Op.Floor -> raise (UnsupportedOp "eval_unop: Floor")
  | F64Op.Trunc -> raise (UnsupportedOp "eval_unop: Trunc")

let i32_binop op e1 e2 =
  match op with
  | I32Op.Add -> BitVector.mk_add e1 e2 `I32Type
  | I32Op.And -> BitVector.mk_and e1 e2 `I32Type
  | I32Op.Or -> BitVector.mk_or e1 e2 `I32Type
  | I32Op.Sub -> BitVector.mk_sub e1 e2 `I32Type
  | I32Op.DivS -> BitVector.mk_div_s e1 e2 `I32Type
  | I32Op.DivU ->  BitVector.mk_div_u e1 e2 `I32Type
  | I32Op.Xor -> BitVector.mk_xor e1 e2 `I32Type
  | I32Op.Mul -> BitVector.mk_mul e1 e2 `I32Type
  | I32Op.Shl -> BitVector.mk_shl e1 e2 `I32Type
  | I32Op.ShrS -> BitVector.mk_shr_s e1 e2 `I32Type
  | I32Op.ShrU -> BitVector.mk_shr_u e1 e2 `I32Type
  | I32Op.RemS -> BitVector.mk_rem_s e1 e2 `I32Type
  | I32Op.RemU -> BitVector.mk_rem_u e1 e2 `I32Type
  | I32Op.Rotl -> failwith "eval I32Binop: TODO Rotl"
  | I32Op.Rotr -> failwith "eval I32Binop: TODO Rotr"

let i64_binop op e1 e2 =
  match op with
  | I64Op.Add -> BitVector.mk_add e1 e2 `I64Type
  | I64Op.And -> BitVector.mk_and e1 e2 `I64Type
  | I64Op.Or -> BitVector.mk_or e1 e2 `I64Type
  | I64Op.Sub -> BitVector.mk_sub e1 e2 `I64Type
  | I64Op.DivS -> BitVector.mk_div_s e1 e2 `I64Type
  | I64Op.DivU ->  BitVector.mk_div_u e1 e2 `I64Type
  | I64Op.Xor -> BitVector.mk_xor e1 e2 `I64Type
  | I64Op.Mul -> BitVector.mk_mul e1 e2 `I64Type
  | I64Op.Shl -> BitVector.mk_shl e1 e2 `I64Type
  | I64Op.ShrS -> BitVector.mk_shr_s e1 e2 `I64Type
  | I64Op.ShrU -> BitVector.mk_shr_u e1 e2 `I64Type
  | I64Op.RemS -> BitVector.mk_rem_s e1 e2 `I64Type
  | I64Op.RemU -> BitVector.mk_rem_u e1 e2 `I64Type
  | I64Op.Rotl -> failwith "eval I64Binop: TODO Rotl"
  | I64Op.Rotr -> failwith "eval I64Binop: TODO Rotr"

let f32_binop op e1 e2 =
  match op with
  | F32Op.Add -> FloatingPoint.mk_add e1 e2 `F32Type
  | F32Op.Sub -> FloatingPoint.mk_sub e1 e2 `F32Type
  | F32Op.Div -> FloatingPoint.mk_div e1 e2 `F32Type
  | F32Op.Mul -> FloatingPoint.mk_mul e1 e2 `F32Type
  | F32Op.Min -> FloatingPoint.mk_min e1 e2 `F32Type
  | F32Op.Max -> FloatingPoint.mk_max e1 e2 `F32Type
  | F32Op.CopySign -> failwith "eval F32Binop: TODO CopySign"

let f64_binop op e1 e2 =
  match op with
  | F64Op.Add -> FloatingPoint.mk_add e1 e2 `F64Type
  | F64Op.Sub -> FloatingPoint.mk_sub e1 e2 `F64Type
  | F64Op.Div -> FloatingPoint.mk_div e1 e2 `F64Type
  | F64Op.Mul -> FloatingPoint.mk_mul e1 e2 `F64Type
  | F64Op.Min -> FloatingPoint.mk_min e1 e2 `F64Type
  | F64Op.Max -> FloatingPoint.mk_max e1 e2 `F64Type
  | F64Op.CopySign -> failwith "eval F64Binop: TODO CopySign"

let i32_relop op e1 e2 =
  match op with
  | I32Op.Eq -> BitVector.mk_eq e1 e2 `I32Type
  | I32Op.Ne -> BitVector.mk_ne e1 e2 `I32Type
  | I32Op.LtU -> BitVector.mk_lt_u e1 e2 `I32Type
  | I32Op.LtS -> BitVector.mk_lt_s e1 e2 `I32Type
  | I32Op.GtU -> BitVector.mk_gt_u e1 e2 `I32Type
  | I32Op.GtS -> BitVector.mk_gt_s e1 e2 `I32Type
  | I32Op.LeU -> BitVector.mk_le_u e1 e2 `I32Type
  | I32Op.LeS -> BitVector.mk_le_s e1 e2 `I32Type
  | I32Op.GeU -> BitVector.mk_ge_u e1 e2 `I32Type
  | I32Op.GeS -> BitVector.mk_ge_s e1 e2 `I32Type

let i64_relop op e1 e2 =
  match op with
  | I64Op.Eq -> BitVector.mk_eq e1 e2 `I64Type
  | I64Op.Ne -> BitVector.mk_ne e1 e2 `I64Type
  | I64Op.LtU -> BitVector.mk_lt_u e1 e2 `I64Type
  | I64Op.LtS -> BitVector.mk_lt_s e1 e2 `I64Type
  | I64Op.GtU -> BitVector.mk_gt_u e1 e2 `I64Type
  | I64Op.GtS -> BitVector.mk_gt_s e1 e2 `I64Type
  | I64Op.LeU -> BitVector.mk_le_u e1 e2 `I64Type
  | I64Op.LeS -> BitVector.mk_le_s e1 e2 `I64Type
  | I64Op.GeU -> BitVector.mk_ge_u e1 e2 `I64Type
  | I64Op.GeS -> BitVector.mk_ge_s e1 e2 `I64Type

let f32_relop op e1 e2 =
  match op with
  | F32Op.Eq -> FloatingPoint.mk_eq e1 e2 `F32Type
  | F32Op.Ne -> FloatingPoint.mk_ne e1 e2 `F32Type
  | F32Op.Lt -> FloatingPoint.mk_lt e1 e2 `F32Type
  | F32Op.Gt -> FloatingPoint.mk_gt e1 e2 `F32Type
  | F32Op.Le -> FloatingPoint.mk_le e1 e2 `F32Type
  | F32Op.Ge -> FloatingPoint.mk_ge e1 e2 `F32Type

let f64_relop op e1 e2 =
  match op with
  | F64Op.Eq -> FloatingPoint.mk_eq e1 e2 `F64Type
  | F64Op.Ne -> FloatingPoint.mk_ne e1 e2 `F64Type
  | F64Op.Lt -> FloatingPoint.mk_lt e1 e2 `F64Type
  | F64Op.Gt -> FloatingPoint.mk_gt e1 e2 `F64Type
  | F64Op.Le -> FloatingPoint.mk_le e1 e2 `F64Type
  | F64Op.Ge -> FloatingPoint.mk_ge e1 e2 `F64Type

(* TODO: sign bit *)
let i32_cvtop op s =
  match op with
  (* 64bit integer is taken modulo 2^32 i.e., top 32 bits are lost *)
  | I32Op.WrapI64 -> Extract (s, 4, 0)
  | I32Op.TruncSF32 -> Cvtop (I32 TruncSF32, s)
  | I32Op.TruncUF32 -> Cvtop (I32 TruncUF32, s)
  | I32Op.TruncSF64 -> Cvtop (I32 TruncSF64, s)
  | I32Op.TruncUF64 -> Cvtop (I32 TruncUF64, s)
  | I32Op.ReinterpretFloat -> Cvtop (I32 ReinterpretFloat, s)
  | I32Op.ExtendSI32 -> raise (Eval_numeric.TypeError (1, I32 1l, `I32Type))
  | I32Op.ExtendUI32 -> raise (Eval_numeric.TypeError (1, I32 1l, `I32Type))

let i64_cvtop op s =
  match op with
  | I64Op.ExtendSI32 -> Cvtop (I64 ExtendSI32, s)
  | I64Op.ExtendUI32 -> Cvtop (I64 ExtendUI32, s)
  | I64Op.TruncSF32 -> Cvtop (I64 TruncSF32, s)
  | I64Op.TruncUF32 -> Cvtop (I64 TruncUF32, s)
  | I64Op.TruncSF64 -> Cvtop (I64 TruncSF64, s)
  | I64Op.TruncUF64 -> Cvtop (I64 TruncUF64, s)
  | I64Op.ReinterpretFloat -> Cvtop (I64 ReinterpretFloat, s)
  | I64Op.WrapI64 -> raise (Eval_numeric.TypeError (1, I64 1L, `I64Type))

let f32_cvtop op s =
  match op with
  | F32Op.DemoteF64 -> Cvtop (F32 DemoteF64, s)
  | F32Op.ConvertSI32 -> Cvtop (F32 ConvertSI32, s)
  | F32Op.ConvertUI32 -> Cvtop (F32 ConvertUI32, s)
  | F32Op.ConvertSI64 -> Cvtop (F32 ConvertSI64, s)
  | F32Op.ConvertUI64 -> Cvtop (F32 ConvertUI64, s)
  | F32Op.ReinterpretInt -> Cvtop (F32 ReinterpretInt, s)
  | F32Op.PromoteF32 -> raise (Eval_numeric.TypeError (1, F32 1l, `F32Type))

let f64_cvtop op s =
  match op with
  | F64Op.PromoteF32 -> Cvtop (F64 PromoteF32, s)
  | F64Op.ConvertSI32 -> Cvtop (F64 ConvertSI32, s)
  | F64Op.ConvertUI32 -> Cvtop (F64 ConvertUI32, s)
  | F64Op.ConvertSI64 -> Cvtop (F64 ConvertSI64, s)
  | F64Op.ConvertUI64 -> Cvtop (F64 ConvertUI64, s)
  | F64Op.ReinterpretInt -> Cvtop (F64 ReinterpretInt, s)
  | F64Op.DemoteF64 -> raise (Eval_numeric.TypeError (1, F64 1L, `F64Type))
