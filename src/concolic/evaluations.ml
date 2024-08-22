open Common.Evaluations
open Smtml
open Ty
open Expr
open Value
open Interpreter.Ast

(*  Evaluate a unary operation  *)
let eval_unop ((c, s) : Num.t * Expr.t) (op : Interpreter.Ast.unop) :
  Num.t * Expr.t =
  let open Expr in
  let open Value in
  let concrete =
    of_value (Interpreter.Eval_numeric.eval_unop op (to_value c))
  in
  let symbolic =
    match Expr.view s with
    | Val (Num _) -> Expr.value (Num concrete)
    | _ -> (
      match op with
      | Interpreter.Values.F32 x -> f32_unop x s
      | Interpreter.Values.F64 x -> f64_unop x s
      | Interpreter.Values.I32 _ | Interpreter.Values.I64 _ ->
        raise (Unsupported_op "eval_unop: ints") )
  in
  (concrete, symbolic)

(*  Evaluate a binary operation *)
let eval_binop ((c1, s1) : Num.t * Expr.t) ((c2, s2) : Num.t * Expr.t)
  (op : Interpreter.Ast.binop) : Num.t * Expr.t =
  let concrete =
    of_value
      (Interpreter.Eval_numeric.eval_binop op (to_value c1) (to_value c2))
  in
  let symbolic =
    match (Expr.view s1, Expr.view s2) with
    | Val (Num _), Val (Num _) -> Expr.value (Num concrete)
    | _ -> (
      match op with
      | Interpreter.Values.I32 x -> i32_binop x s1 s2
      | Interpreter.Values.I64 x -> i64_binop x s1 s2
      | Interpreter.Values.F32 x -> f32_binop x s1 s2
      | Interpreter.Values.F64 x -> f64_binop x s1 s2 )
  in
  (concrete, symbolic)

(*  Evaluate a test operation  *)
let eval_testop ((c, s) : Num.t * Expr.t) (op : testop) : Num.t * Expr.t =
  let concrete =
    Num.num_of_bool (Interpreter.Eval_numeric.eval_testop op (to_value c))
  in
  let symbolic =
    match Expr.view s with
    | Val (Num _) -> Expr.value (Num concrete)
    | Ptr { base = _; offset } when not (Expr.is_symbolic offset) ->
      Expr.value (Num concrete)
    | _ -> (
      match op with
      | Interpreter.Values.I32 I32Op.Eqz ->
        relop Ty_bool Eq s (Expr.value (Num (Num.I32 0l)))
      | Interpreter.Values.I64 I64Op.Eqz ->
        relop Ty_bool Eq s (Expr.value (Num (Num.I64 0L)))
      | _ -> failwith "eval_testop: floats" )
  in
  (concrete, symbolic)

(*  Evaluate a relative operation  *)
let eval_relop ((c1, s1) : Num.t * Expr.t) ((c2, s2) : Num.t * Expr.t)
  (op : Interpreter.Ast.relop) : Num.t * Expr.t =
  let concrete =
    Num.num_of_bool
      (Interpreter.Eval_numeric.eval_relop op (to_value c1) (to_value c2))
  in
  let symbolic =
    match (Expr.view s1, Expr.view s2) with
    | Val (Num _), Val (Num _) -> Expr.value (Num concrete)
    | _ -> (
      match op with
      | Interpreter.Values.I32 x -> i32_relop x s1 s2
      | Interpreter.Values.I64 x -> i64_relop x s1 s2
      | Interpreter.Values.F32 x -> f32_relop x s1 s2
      | Interpreter.Values.F64 x -> f64_relop x s1 s2 )
  in
  (concrete, symbolic)

let eval_cvtop (op : Interpreter.Ast.cvtop) ((c, s) : Num.t * Expr.t) :
  Num.t * Expr.t =
  let concrete =
    of_value (Interpreter.Eval_numeric.eval_cvtop op (to_value c))
  in
  let symbolic =
    match Expr.view s with
    | Val (Num _) -> Expr.value (Num concrete)
    | _ -> (
      let (* dispatch cvtop func *)
      open Interpreter in
      match op with
      | Values.I32 x -> i32_cvtop x s
      | Values.I64 x -> i64_cvtop x s
      | Values.F32 x -> f32_cvtop x s
      | Values.F64 x -> f64_cvtop x s )
  in
  (concrete, symbolic)
