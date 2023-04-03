open Encoding
open Types

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
