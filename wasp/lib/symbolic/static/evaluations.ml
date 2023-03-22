open Syntax.I32
open Syntax.I64
open Syntax.F32
open Syntax.F64
open Syntax.Val

open Interpreter
open Interpreter.Ast


(* TODO: this file and wasp/symbolic/evaluations.ml share a lot
  of code, needs to be modularized
 *)

exception UnsupportedOp of string

(*  Evaluate a unary operation  *)
let eval_unop (e : sym_expr) (op : unop) : sym_expr =
  let f32_unop op e =
    begin match op with
    | F32Op.Neg     -> F32Unop (F32Neg, e)
    | F32Op.Abs     -> F32Unop (F32Abs, e)
    | F32Op.Sqrt    -> F32Unop (F32Sqrt, e)
    | F32Op.Nearest -> F32Unop (F32Nearest, e)
    | F32Op.Ceil    -> raise (UnsupportedOp "eval_unop: Ceil")
    | F32Op.Floor   -> raise (UnsupportedOp "eval_unop: Floor")
    | F32Op.Trunc   -> raise (UnsupportedOp "eval_unop: Trunc")
    end
  in
  let f64_unop op e =
    begin match op with
    | F64Op.Neg     -> F64Unop (F64Neg, e)
    | F64Op.Abs     -> F64Unop (F64Abs, e)
    | F64Op.Sqrt    -> F64Unop (F64Sqrt, e)
    | F64Op.Nearest -> F64Unop (F64Nearest, e)
    | F64Op.Ceil    -> raise (UnsupportedOp "eval_unop: Ceil")
    | F64Op.Floor   -> raise (UnsupportedOp "eval_unop: Floor")
    | F64Op.Trunc   -> raise (UnsupportedOp "eval_unop: Trunc")
    end
  in
  match e with
  | Value c -> Value (Eval_numeric.eval_unop op c)
  | _ -> match op with
    | Values.F32 x -> f32_unop x e
    | Values.F64 x -> f64_unop x e
		| Values.I32 _ | Values.I64 _ -> raise (UnsupportedOp "eval_unop: ints")

(*  Evaluate a binary operation *)
let eval_binop (s1 : sym_expr) (s2 : sym_expr) (op : Ast.binop) : sym_expr =
  let i32_binop op e1 e2 =
    begin match op with
    | I32Op.Add  -> I32Binop (I32Add , e1, e2)
    | I32Op.And  -> I32Binop (I32And , e1, e2)
    | I32Op.Or   -> I32Binop (I32Or  , e1, e2)
    | I32Op.Sub  -> I32Binop (I32Sub , e1, e2)
    | I32Op.DivS -> I32Binop (I32DivS, e1, e2)
    | I32Op.DivU -> I32Binop (I32DivU, e1, e2)
    | I32Op.Xor  -> I32Binop (I32Xor , e1, e2)
    | I32Op.Mul  -> I32Binop (I32Mul , e1, e2)
    | I32Op.Shl  -> I32Binop (I32Shl , e1, e2)
    | I32Op.ShrS -> I32Binop (I32ShrS, e1, e2)
    | I32Op.ShrU -> I32Binop (I32ShrU, e1, e2)
    | I32Op.RemS -> I32Binop (I32RemS, e1, e2)
    | I32Op.RemU -> I32Binop (I32RemU, e1, e2)
    | I32Op.Rotl -> failwith "eval I32Binop: TODO Rotl"
    | I32Op.Rotr -> failwith "eval I32Binop: TODO Rotr"
    end
  in
  let i64_binop op e1 e2 =
    begin match op with
    | I64Op.Add  -> I64Binop (I64Add , e1, e2)
    | I64Op.And  -> I64Binop (I64And , e1, e2)
    | I64Op.Or   -> I64Binop (I64Or  , e1, e2)
    | I64Op.Sub  -> I64Binop (I64Sub , e1, e2)
    | I64Op.DivS -> I64Binop (I64DivS, e1, e2)
    | I64Op.DivU -> I64Binop (I64DivU, e1, e2)
    | I64Op.Xor  -> I64Binop (I64Xor , e1, e2)
    | I64Op.Mul  -> I64Binop (I64Mul , e1, e2)
    | I64Op.RemS -> I64Binop (I64RemS, e1, e2)
    | I64Op.RemU -> I64Binop (I64RemU, e1, e2)
    | I64Op.Shl  -> I64Binop (I64Shl , e1, e2)
    | I64Op.ShrS -> I64Binop (I64ShrS, e1, e2)
    | I64Op.ShrU -> I64Binop (I64ShrU, e1, e2)
    | I64Op.Rotl -> failwith "eval I64Binop: TODO Rotl"
    | I64Op.Rotr -> failwith "eval I64Binop: TODO Rotr"
    end
  in
  let f32_binop op e1 e2 =
    begin match op with
    | F32Op.Add  -> F32Binop (F32Add, e1, e2)
    | F32Op.Sub  -> F32Binop (F32Sub, e1, e2)
    | F32Op.Div  -> F32Binop (F32Div, e1, e2)
    | F32Op.Mul  -> F32Binop (F32Mul, e1, e2)
    | F32Op.Min  -> F32Binop (F32Min, e1, e2)
    | F32Op.Max  -> F32Binop (F32Max, e1, e2)
    | F32Op.CopySign -> failwith "eval F32Binop: TODO CopySign"
    end
  in
  let f64_binop op e1 e2 =
    begin match op with
    | F64Op.Add  -> F64Binop (F64Add, e1, e2)
    | F64Op.Sub  -> F64Binop (F64Sub, e1, e2)
    | F64Op.Div  -> F64Binop (F64Div, e1, e2)
    | F64Op.Mul  -> F64Binop (F64Mul, e1, e2)
    | F64Op.Min  -> F64Binop (F64Min, e1, e2)
    | F64Op.Max  -> F64Binop (F64Max, e1, e2)
    | F64Op.CopySign -> failwith "eval F64Binop: TODO CopySign"
    end
  in
	let s =
    begin match s1, s2 with
    | Value c1, Value c2 -> Value (Eval_numeric.eval_binop op c1 c2)
		| _ -> (* dispatch *)
        begin match op with
        | Values.I32 x -> i32_binop x s1 s2
        | Values.I64 x -> i64_binop x s1 s2
        | Values.F32 x -> f32_binop x s1 s2
        | Values.F64 x -> f64_binop x s1 s2
        end
    end
  in s

(*  Evaluate a test operation  *)
let eval_testop (e : sym_expr) (op : testop) : sym_expr =
  begin match e with
  | Value c -> Value (Values.value_of_bool (Eval_numeric.eval_testop op c))
  | SymPtr (b, Value (Values.I32 o)) ->
    let c = Values.I32 (Int32.add b o) in
    Value (Values.value_of_bool (Eval_numeric.eval_testop op c))
  | _ ->
      begin match op with
      | Values.I32 I32Op.Eqz -> I32Relop (I32Eq, e, Value (Values.I32 0l))
      | Values.I64 I64Op.Eqz -> I64Relop (I64Eq, e, Value (Values.I64 0L))
      | Values.F32 _ | Values.F64 _ -> failwith "eval_testop: floats"
      end
  end

(*  Evaluate a relative operation  *)
let eval_relop (s1 : sym_expr) (s2 : sym_expr) (op : Ast.relop) : sym_expr =
  let i32_relop op e1 e2 =
    begin match op with
    | I32Op.Eq  -> I32Relop (I32Eq , e1, e2)
    | I32Op.Ne  -> I32Relop (I32Ne , e1, e2)
    | I32Op.LtU -> I32Relop (I32LtU, e1, e2)
    | I32Op.LtS -> I32Relop (I32LtS, e1, e2)
    | I32Op.GtU -> I32Relop (I32GtU, e1, e2)
    | I32Op.GtS -> I32Relop (I32GtS, e1, e2)
    | I32Op.LeU -> I32Relop (I32LeU, e1, e2)
    | I32Op.LeS -> I32Relop (I32LeS, e1, e2)
    | I32Op.GeU -> I32Relop (I32GeU, e1, e2)
    | I32Op.GeS -> I32Relop (I32GeS, e1, e2)
    end
  in
  let i64_relop op e1 e2 =
    begin match op with
    | I64Op.Eq  -> I64Relop (I64Eq , e1, e2)
    | I64Op.Ne  -> I64Relop (I64Ne , e1, e2)
    | I64Op.LtU -> I64Relop (I64LtU, e1, e2)
    | I64Op.LtS -> I64Relop (I64LtS, e1, e2)
    | I64Op.GtU -> I64Relop (I64GtU, e1, e2)
    | I64Op.GtS -> I64Relop (I64GtS, e1, e2)
    | I64Op.LeU -> I64Relop (I64LeU, e1, e2)
    | I64Op.LeS -> I64Relop (I64LeS, e1, e2)
    | I64Op.GeU -> I64Relop (I64GeU, e1, e2)
    | I64Op.GeS -> I64Relop (I64GeS, e1, e2)
    end
  in
  let f32_relop op e1 e2 =
    begin match op with
    | F32Op.Eq  -> F32Relop (F32Eq, e1, e2)
    | F32Op.Ne  -> F32Relop (F32Ne, e1, e2)
    | F32Op.Lt  -> F32Relop (F32Lt, e1, e2)
    | F32Op.Gt  -> F32Relop (F32Gt, e1, e2)
    | F32Op.Le  -> F32Relop (F32Le, e1, e2)
    | F32Op.Ge  -> F32Relop (F32Ge, e1, e2)
    end
  in
  let f64_relop op e1 e2 =
    begin match op with
    | F64Op.Eq  -> F64Relop (F64Eq, e1, e2)
    | F64Op.Ne  -> F64Relop (F64Ne, e1, e2)
    | F64Op.Lt  -> F64Relop (F64Lt, e1, e2)
    | F64Op.Gt  -> F64Relop (F64Gt, e1, e2)
    | F64Op.Le  -> F64Relop (F64Le, e1, e2)
    | F64Op.Ge  -> F64Relop (F64Ge, e1, e2)
    end
  in
	let s : sym_expr =
    begin match s1, s2 with
    | Value c1, Value c2 -> Value (Values.value_of_bool (Eval_numeric.eval_relop op c1 c2))
		| _ -> (* dispatch *)
        begin match op with
        | Values.I32 x -> i32_relop x s1 s2
        | Values.I64 x -> i64_relop x s1 s2
        | Values.F32 x -> f32_relop x s1 s2
        | Values.F64 x -> f64_relop x s1 s2
        end
    end
  in s

let eval_cvtop (op : Ast.cvtop) (s : sym_expr) : sym_expr =
  (* TODO: sign bit *)
  let i32_cvtop op s =
    match op with
    (* 64bit integer is taken modulo 2^32 i.e., top 32 bits are lost *)
    | I32Op.WrapI64 -> Extract (s, 4, 0)
    | I32Op.TruncSF32 -> I32Cvtop (I32TruncSF32, s)
    | I32Op.TruncUF32 -> I32Cvtop (I32TruncUF32, s)
    | I32Op.TruncSF64 -> I32Cvtop (I32TruncSF64, s)
    | I32Op.TruncUF64 -> I32Cvtop (I32TruncUF64, s)
    | I32Op.ReinterpretFloat -> I32Cvtop (I32ReinterpretFloat, s)
    (* | I32Op.ExtendSI32 -> raise (Eval_numeric.TypeError (1, c, Types.I32Type)) *)
    | I32Op.ExtendSI32 -> failwith "don't have a c for TypeError"
    (* | I32Op.ExtendUI32 -> raise (Eval_numeric.TypeError (1, c, Types.I32Type)) *)
    | I32Op.ExtendUI32 -> failwith "don't have a c for TypeError"
  in
  let i64_cvtop op s =
    match op with
    | I64Op.ExtendSI32 -> I64Cvtop (I64ExtendSI32, s)
    | I64Op.ExtendUI32 -> I64Cvtop (I64ExtendUI32, s)
    | I64Op.TruncSF32  -> I64Cvtop (I64TruncSF32, s)
    | I64Op.TruncUF32  -> I64Cvtop (I64TruncUF32, s)
    | I64Op.TruncSF64  -> I64Cvtop (I64TruncSF64, s)
    | I64Op.TruncUF64  -> I64Cvtop (I64TruncUF64, s)
    | I64Op.ReinterpretFloat -> I64Cvtop (I64ReinterpretFloat, s)
    (* | I64Op.WrapI64 -> raise (Eval_numeric.TypeError (1, c, Types.I64Type)) *)
    | I64Op.WrapI64 -> failwith "don't have a c for TypeError"
  in
  let f32_cvtop op s =
    match op with
    | F32Op.DemoteF64   -> F32Cvtop (F32DemoteF64, s)
    | F32Op.ConvertSI32 -> F32Cvtop (F32ConvertSI32, s)
    | F32Op.ConvertUI32 -> F32Cvtop (F32ConvertUI32, s)
    | F32Op.ConvertSI64 -> F32Cvtop (F32ConvertSI64, s)
    | F32Op.ConvertUI64 -> F32Cvtop (F32ConvertUI64, s)
    | F32Op.ReinterpretInt -> F32Cvtop (F32ReinterpretInt, s)
    (* | F32Op.PromoteF32 -> raise (Eval_numeric.TypeError (1, c, Types.F32Type)) *)
    | F32Op.PromoteF32 -> failwith "don't have a c for TypeError"
  in
  let f64_cvtop op s =
    match op with
    | F64Op.PromoteF32  -> F64Cvtop (F64PromoteF32, s)
    | F64Op.ConvertSI32 -> F64Cvtop (F64ConvertSI32, s)
    | F64Op.ConvertUI32 -> F64Cvtop (F64ConvertUI32, s)
    | F64Op.ConvertSI64 -> F64Cvtop (F64ConvertSI64, s)
    | F64Op.ConvertUI64 -> F64Cvtop (F64ConvertUI64, s)
    | F64Op.ReinterpretInt -> F64Cvtop (F64ReinterpretInt, s)
    (* | F64Op.DemoteF64 -> raise (Eval_numeric.TypeError (1, c, Types.F64Type)) *)
    | F64Op.DemoteF64 -> failwith "don't have a c for TypeError"
  in
  let s =
    begin match s with
    | Value c -> Value (Eval_numeric.eval_cvtop op c)
    | _ ->
        (* dispatch cvtop func *)
        begin match op with
        | Values.I32 x -> i32_cvtop x s
        | Values.I64 x -> i64_cvtop x s
        | Values.F32 x -> f32_cvtop x s
        | Values.F64 x -> f64_cvtop x s
        end
    end
  in s
