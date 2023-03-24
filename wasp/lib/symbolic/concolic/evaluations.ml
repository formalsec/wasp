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

let to_num_type (t : Interpreter.Types.value_type) : num_type =
  let open Interpreter in
  match t with
  | Types.I32Type -> I32Type
  | Types.I64Type -> I64Type
  | Types.F32Type -> F32Type
  | Types.F64Type -> F64Type

(*  Evaluate a unary operation  *)
let eval_unop (e : Expression.value) (op : Interpreter.Ast.unop) : value =
  let f32_unop op e =
    begin match op with
    | F32Op.Neg     -> Unop (F32 Neg, e)
    | F32Op.Abs     -> Unop (F32 Abs, e)
    | F32Op.Sqrt    -> Unop (F32 Sqrt, e)
    | F32Op.Nearest -> Unop (F32 Nearest, e)
    | F32Op.Ceil    -> raise (UnsupportedOp "eval_unop: Ceil")
    | F32Op.Floor   -> raise (UnsupportedOp "eval_unop: Floor")
    | F32Op.Trunc   -> raise (UnsupportedOp "eval_unop: Trunc")
    end
  in
  let f64_unop op e =
    begin match op with
    | F64Op.Neg     -> Unop (F64 Neg, e)
    | F64Op.Abs     -> Unop (F64 Abs, e)
    | F64Op.Sqrt    -> Unop (F64 Sqrt, e)
    | F64Op.Nearest -> Unop (F64 Nearest, e)
    | F64Op.Ceil    -> raise (UnsupportedOp "eval_unop: Ceil")
    | F64Op.Floor   -> raise (UnsupportedOp "eval_unop: Floor")
    | F64Op.Trunc   -> raise (UnsupportedOp "eval_unop: Trunc")
    end
  in
  let (c, s) = e in
  let c' = of_value (Interpreter.Eval_numeric.eval_unop op (to_value c)) in
  let s' =
  begin match s with
    | Num _ -> Num c'
    | _ -> (* dispatch *)
        let open Interpreter in
        begin match op with
        | Values.F32 x -> f32_unop x s
        | Values.F64 x -> f64_unop x s
        | Values.I32 _
        | Values.I64 _ ->
            raise (UnsupportedOp "eval_unop: ints")
        end
    end
  in (c', s')

(*  Evaluate a binary operation *)
let eval_binop (e1 : value) (e2 : value) (op : Interpreter.Ast.binop) : value =
  let i32_binop op e1 e2 =
    begin match op with
    | I32Op.Add  -> Binop (I32 Add , e1, e2)
    | I32Op.And  -> Binop (I32 And , e1, e2)
    | I32Op.Or   -> Binop (I32 Or  , e1, e2)
    | I32Op.Sub  -> Binop (I32 Sub , e1, e2)
    | I32Op.DivS -> Binop (I32 DivS, e1, e2)
    | I32Op.DivU -> Binop (I32 DivU, e1, e2)
    | I32Op.Xor  -> Binop (I32 Xor , e1, e2)
    | I32Op.Mul  -> Binop (I32 Mul , e1, e2)
    | I32Op.Shl  -> Binop (I32 Shl , e1, e2)
    | I32Op.ShrS -> Binop (I32 ShrS, e1, e2)
    | I32Op.ShrU -> Binop (I32 ShrU, e1, e2)
    | I32Op.RemS -> Binop (I32 RemS, e1, e2)
    | I32Op.RemU -> Binop (I32 RemU, e1, e2)
    | I32Op.Rotl -> failwith "eval I32Binop: TODO Rotl"
    | I32Op.Rotr -> failwith "eval I32Binop: TODO Rotr"
    end
  in
  let i64_binop op e1 e2 =
    begin match op with
    | I64Op.Add  -> Binop (I64 Add , e1, e2)
    | I64Op.And  -> Binop (I64 And , e1, e2)
    | I64Op.Or   -> Binop (I64 Or  , e1, e2)
    | I64Op.Sub  -> Binop (I64 Sub , e1, e2)
    | I64Op.DivS -> Binop (I64 DivS, e1, e2)
    | I64Op.DivU -> Binop (I64 DivU, e1, e2)
    | I64Op.Xor  -> Binop (I64 Xor , e1, e2)
    | I64Op.Mul  -> Binop (I64 Mul , e1, e2)
    | I64Op.RemS -> Binop (I64 RemS, e1, e2)
    | I64Op.RemU -> Binop (I64 RemU, e1, e2)
    | I64Op.Shl  -> Binop (I64 Shl , e1, e2)
    | I64Op.ShrS -> Binop (I64 ShrS, e1, e2)
    | I64Op.ShrU -> Binop (I64 ShrU, e1, e2)
    | I64Op.Rotl -> failwith "eval I64Binop: TODO Rotl"
    | I64Op.Rotr -> failwith "eval I64Binop: TODO Rotr"
    end
  in
  let f32_binop op e1 e2 =
    begin match op with
    | F32Op.Add  -> Binop (F32 Add, e1, e2)
    | F32Op.Sub  -> Binop (F32 Sub, e1, e2)
    | F32Op.Div  -> Binop (F32 Div, e1, e2)
    | F32Op.Mul  -> Binop (F32 Mul, e1, e2)
    | F32Op.Min  -> Binop (F32 Min, e1, e2)
    | F32Op.Max  -> Binop (F32 Max, e1, e2)
    | F32Op.CopySign -> failwith "eval F32Binop: TODO CopySign"
    end
  in
  let f64_binop op e1 e2 =
    begin match op with
    | F64Op.Add  -> Binop (F64 Add, e1, e2)
    | F64Op.Sub  -> Binop (F64 Sub, e1, e2)
    | F64Op.Div  -> Binop (F64 Div, e1, e2)
    | F64Op.Mul  -> Binop (F64 Mul, e1, e2)
    | F64Op.Min  -> Binop (F64 Min, e1, e2)
    | F64Op.Max  -> Binop (F64 Max, e1, e2)
    | F64Op.CopySign -> failwith "eval F64Binop: TODO CopySign"
    end
  in
  let (c1, s1) = e1
  and (c2, s2) = e2 in
  let c =
    of_value
      (Interpreter.Eval_numeric.eval_binop op
        (to_value c1) (to_value c2))
  in
  let s =
    begin match s1, s2 with
    | Num _, Num _ -> Num c
    | _ -> (* dispatch *)
        let open Interpreter in
        begin match op with
        | Values.I32 x -> i32_binop x s1 s2
        | Values.I64 x -> i64_binop x s1 s2
        | Values.F32 x -> f32_binop x s1 s2
        | Values.F64 x -> f64_binop x s1 s2
        end
    end
  in (c, s)

(*  Evaluate a test operation  *)
let eval_testop (e : value) (op : testop) : value =
  let (c, s) = e in
  let c' =
    Num.num_of_bool
      (Interpreter.Eval_numeric.eval_testop op (to_value c))
  in
  let s' =
  (match s with
    | Num _ -> Num c'
    | SymPtr (b, Num _) -> Num c'
    | _ -> (
        match op with
        | Interpreter.Values.I32 I32Op.Eqz ->
            Relop (I32 Eq, s, Num (I32 0l))
        | Interpreter.Values.I64 I64Op.Eqz ->
            Relop (I64 Eq, s, Num (I64 0L))
        | _ -> failwith "eval_testop: floats"))
  in (c', s')

(*  Evaluate a relative operation  *)
let eval_relop (e1 : value) (e2 : value) (op : Interpreter.Ast.relop) : value =
  let i32_relop op e1 e2 =
    begin match op with
    | I32Op.Eq  -> Relop (I32 Eq , e1, e2)
    | I32Op.Ne  -> Relop (I32 Ne , e1, e2)
    | I32Op.LtU -> Relop (I32 LtU, e1, e2)
    | I32Op.LtS -> Relop (I32 LtS, e1, e2)
    | I32Op.GtU -> Relop (I32 GtU, e1, e2)
    | I32Op.GtS -> Relop (I32 GtS, e1, e2)
    | I32Op.LeU -> Relop (I32 LeU, e1, e2)
    | I32Op.LeS -> Relop (I32 LeS, e1, e2)
    | I32Op.GeU -> Relop (I32 GeU, e1, e2)
    | I32Op.GeS -> Relop (I32 GeS, e1, e2)
    end
  in
  let i64_relop op e1 e2 =
    begin match op with
    | I64Op.Eq  -> Relop (I64 Eq , e1, e2)
    | I64Op.Ne  -> Relop (I64 Ne , e1, e2)
    | I64Op.LtU -> Relop (I64 LtU, e1, e2)
    | I64Op.LtS -> Relop (I64 LtS, e1, e2)
    | I64Op.GtU -> Relop (I64 GtU, e1, e2)
    | I64Op.GtS -> Relop (I64 GtS, e1, e2)
    | I64Op.LeU -> Relop (I64 LeU, e1, e2)
    | I64Op.LeS -> Relop (I64 LeS, e1, e2)
    | I64Op.GeU -> Relop (I64 GeU, e1, e2)
    | I64Op.GeS -> Relop (I64 GeS, e1, e2)
    end
  in
  let f32_relop op e1 e2 =
    begin match op with
    | F32Op.Eq  -> Relop (F32 Eq, e1, e2)
    | F32Op.Ne  -> Relop (F32 Ne, e1, e2)
    | F32Op.Lt  -> Relop (F32 Lt, e1, e2)
    | F32Op.Gt  -> Relop (F32 Gt, e1, e2)
    | F32Op.Le  -> Relop (F32 Le, e1, e2)
    | F32Op.Ge  -> Relop (F32 Ge, e1, e2)
    end
  in
  let f64_relop op e1 e2 =
    begin match op with
    | F64Op.Eq  -> Relop (F64 Eq, e1, e2)
    | F64Op.Ne  -> Relop (F64 Ne, e1, e2)
    | F64Op.Lt  -> Relop (F64 Lt, e1, e2)
    | F64Op.Gt  -> Relop (F64 Gt, e1, e2)
    | F64Op.Le  -> Relop (F64 Le, e1, e2)
    | F64Op.Ge  -> Relop (F64 Ge, e1, e2)
    end
  in
  let (c1, s1) = e1
  and (c2, s2) = e2 in
  let c =
    Num.num_of_bool
      (Interpreter.Eval_numeric.eval_relop op (to_value c1)
        (to_value c2))
  in
  let s =
    begin match s1, s2 with
    | Num _, Num _ -> Num c
    | _ -> (* dispatch *)
        let open Interpreter in
        begin match op with
        | Values.I32 x -> i32_relop x s1 s2
        | Values.I64 x -> i64_relop x s1 s2
        | Values.F32 x -> f32_relop x s1 s2
        | Values.F64 x -> f64_relop x s1 s2
        end
    end
  in (c, s)

let eval_cvtop (op : Interpreter.Ast.cvtop) (e : value) : value =
  (* TODO: sign bit *)
  let i32_cvtop op e =
    let (c, s) = e in
    match op with
    (* 64bit integer is taken modulo 2^32 i.e., top 32 bits are lost *)
    | I32Op.WrapI64 -> Extract (s, 4, 0)
    | I32Op.TruncSF32 -> Cvtop (I32 TruncSF32, s)
    | I32Op.TruncUF32 -> Cvtop (I32 TruncUF32, s)
    | I32Op.TruncSF64 -> Cvtop (I32 TruncSF64, s)
    | I32Op.TruncUF64 -> Cvtop (I32 TruncUF64, s)
    | I32Op.ReinterpretFloat -> Cvtop (I32 ReinterpretFloat, s)
    | I32Op.ExtendSI32 -> raise (Eval_numeric.TypeError (1, c, Types.I32Type))
    | I32Op.ExtendUI32 -> raise (Eval_numeric.TypeError (1, c, Types.I32Type))
  in
  let i64_cvtop op e =
    let (c, s) = e in
    match op with
    | I64Op.ExtendSI32 -> Cvtop (I64 ExtendSI32, s)
    | I64Op.ExtendUI32 -> Cvtop (I64 ExtendUI32, s)
    | I64Op.TruncSF32  -> Cvtop (I64 TruncSF32, s)
    | I64Op.TruncUF32  -> Cvtop (I64 TruncUF32, s)
    | I64Op.TruncSF64  -> Cvtop (I64 TruncSF64, s)
    | I64Op.TruncUF64  -> Cvtop (I64 TruncUF64, s)
    | I64Op.ReinterpretFloat -> Cvtop (I64 ReinterpretFloat, s)
    | I64Op.WrapI64 -> raise (Eval_numeric.TypeError (1, c, Types.I64Type))
  in
  let f32_cvtop op e =
    let (c, s) = e in
    match op with
    | F32Op.DemoteF64   -> Cvtop (F32 DemoteF64, s)
    | F32Op.ConvertSI32 -> Cvtop (F32 ConvertSI32, s)
    | F32Op.ConvertUI32 -> Cvtop (F32 ConvertUI32, s)
    | F32Op.ConvertSI64 -> Cvtop (F32 ConvertSI64, s)
    | F32Op.ConvertUI64 -> Cvtop (F32 ConvertUI64, s)
    | F32Op.ReinterpretInt -> Cvtop (F32 ReinterpretInt, s)
    | F32Op.PromoteF32 -> raise (Eval_numeric.TypeError (1, c, Types.F32Type))
  in
  let f64_cvtop op e =
    let (c, s) = e in
    match op with
    | F64Op.PromoteF32  -> Cvtop (F64 PromoteF32, s)
    | F64Op.ConvertSI32 -> Cvtop (F64 ConvertSI32, s)
    | F64Op.ConvertUI32 -> Cvtop (F64 ConvertUI32, s)
    | F64Op.ConvertSI64 -> Cvtop (F64 ConvertSI64, s)
    | F64Op.ConvertUI64 -> Cvtop (F64 ConvertUI64, s)
    | F64Op.ReinterpretInt -> Cvtop (F64 ReinterpretInt, s)
    | F64Op.DemoteF64 -> raise (Eval_numeric.TypeError (1, c, Types.F64Type))
  in
  let (c, s) = e in
  let c = of_value (Interpreter.Eval_numeric.eval_cvtop op (to_value c)) in
  let s =
    begin match s with
    | Num _ -> Num c
    | _ ->
        (* dispatch cvtop func *)
        let open Interpreter in
        begin match op with
        | Values.I32 x -> i32_cvtop x e
        | Values.I64 x -> i64_cvtop x e
        | Values.F32 x -> f32_cvtop x e
        | Values.F64 x -> f64_cvtop x e
        end
    end
  in (c, s)

