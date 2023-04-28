open Common.Evaluations
open Encoding
open Value
open Expression
open Types
open I64
open Interpreter.Ast

(*  Evaluate a unary operation  *)
let eval_unop (e : Num.t * expr) (op : Interpreter.Ast.unop) : Num.t * expr =
  let c, s = e in
  let c' = of_value (Interpreter.Eval_numeric.eval_unop op (to_value c)) in
  let s' =
    match s with
    | Val (Num _) -> Val (Num c')
    | _ -> (
        let (* dispatch *)
        open Interpreter in
        match op with
        | Values.F32 x -> f32_unop x s
        | Values.F64 x -> f64_unop x s
        | Values.I32 _ | Values.I64 _ -> raise (UnsupportedOp "eval_unop: ints")
        )
  in
  (c', s')

(*  Evaluate a binary operation *)
let eval_binop (e1 : Num.t * t) (e2 : Num.t * t) (op : Interpreter.Ast.binop) :
    Num.t * t =
  let c1, s1 = e1 and c2, s2 = e2 in
  let c =
    of_value
      (Interpreter.Eval_numeric.eval_binop op (to_value c1) (to_value c2))
  in
  let s =
    match (s1, s2) with
    | Val (Num _), Val (Num _) -> Val (Num c)
    | _ -> (
        let (* dispatch *)
        open Interpreter in
        match op with
        | Values.I32 x -> i32_binop x s1 s2
        | Values.I64 x -> i64_binop x s1 s2
        | Values.F32 x -> f32_binop x s1 s2
        | Values.F64 x -> f64_binop x s1 s2)
  in
  (c, s)

(*  Evaluate a test operation  *)
let eval_testop (e : Num.t * t) (op : testop) : Num.t * t =
  let c, s = e in
  let c' =
    Num.num_of_bool (Interpreter.Eval_numeric.eval_testop op (to_value c))
  in
  let s' =
    match s with
    | Val (Num _) -> Val (Num c')
    | SymPtr (b, Val (Num _)) -> Val (Num c')
    | _ -> (
        match op with
        | Interpreter.Values.I32 I32Op.Eqz ->
            Relop (I32 Eq, s, Val (Num (I32 0l)))
        | Interpreter.Values.I64 I64Op.Eqz ->
            Relop (I64 Eq, s, Val (Num (I64 0L)))
        | _ -> failwith "eval_testop: floats")
  in
  (c', s')

(*  Evaluate a relative operation  *)
let eval_relop (e1 : Num.t * t) (e2 : Num.t * t) (op : Interpreter.Ast.relop) :
    Num.t * t =
  let c1, s1 = e1 and c2, s2 = e2 in
  let c =
    Num.num_of_bool
      (Interpreter.Eval_numeric.eval_relop op (to_value c1) (to_value c2))
  in
  let s =
    match (s1, s2) with
    | Val (Num _), Val (Num _) -> Val (Num c)
    | _ -> (
        let (* dispatch *)
        open Interpreter in
        match op with
        | Values.I32 x -> i32_relop x s1 s2
        | Values.I64 x -> i64_relop x s1 s2
        | Values.F32 x -> f32_relop x s1 s2
        | Values.F64 x -> f64_relop x s1 s2)
  in
  (c, s)

let eval_cvtop (op : Interpreter.Ast.cvtop) (e : Num.t * t) : Num.t * t =
  let c, s = e in
  let c = of_value (Interpreter.Eval_numeric.eval_cvtop op (to_value c)) in
  let s =
    match s with
    | Val (Num _) -> Val (Num c)
    | _ -> (
        let (* dispatch cvtop func *)
        open Interpreter in
        match op with
        | Values.I32 x -> i32_cvtop x s
        | Values.I64 x -> i64_cvtop x s
        | Values.F32 x -> f32_cvtop x s
        | Values.F64 x -> f64_cvtop x s)
  in
  (c, s)
