open Si32
open Si64
open Sf32
open Sf64

open Ast
open Symvalue

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
