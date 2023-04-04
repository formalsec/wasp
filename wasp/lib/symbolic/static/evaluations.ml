open Common.Evaluations
open Encoding
open Expression
open Types
open I64
open Interpreter.Ast

(*  Evaluate a unary operation  *)
let eval_unop (e : expr) (op : unop) : expr =
  match e with
  | Val (Num c) ->
      Val (Num (of_value (Interpreter.Eval_numeric.eval_unop op (to_value c))))
  | _ -> (
      let open Interpreter in
      match op with
      | Values.F32 x -> f32_unop x e
      | Values.F64 x -> f64_unop x e
      | Values.I32 _ | Values.I64 _ -> raise (UnsupportedOp "eval_unop: ints"))

(*  Evaluate a binary operation *)
let eval_binop (s1 : expr) (s2 : expr) (op : binop) : expr =
  let s =
    let open Interpreter in
    match (s1, s2) with
    | Val (Num c1), Val (Num c2) ->
        Val
          (Num
             (of_value (Eval_numeric.eval_binop op (to_value c1) (to_value c2))))
    | _ -> (
        (* dispatch *)
        match op with
        | Values.I32 x -> i32_binop x s1 s2
        | Values.I64 x -> i64_binop x s1 s2
        | Values.F32 x -> f32_binop x s1 s2
        | Values.F64 x -> f64_binop x s1 s2)
  in
  s

(*  Evaluate a test operation  *)
let eval_testop (e : expr) (op : testop) : expr =
  match e with
  | Val (Num c) ->
      Val
        (Num
           (Num.num_of_bool
              (Interpreter.Eval_numeric.eval_testop op (to_value c))))
  | SymPtr (b, Val (Num (I32 o))) ->
      let c : Num.t = I32 (Int32.add b o) in
      Val
        (Num
           (Num.num_of_bool
              (Interpreter.Eval_numeric.eval_testop op (to_value c))))
  | _ -> (
      let open Interpreter in
      match op with
      | Values.I32 I32Op.Eqz -> Relop (I32 Eq, e, Val (Num (I32 0l)))
      | Values.I64 I64Op.Eqz -> Relop (I64 Eq, e, Val (Num (I64 0L)))
      | Values.F32 _ | Values.F64 _ -> failwith "eval_testop: floats")

(*  Evaluate a relative operation  *)
let eval_relop (s1 : expr) (s2 : expr) (op : relop) : expr =
  let s : expr =
    match (s1, s2) with
    | Val (Num c1), Val (Num c2) ->
        Val
          (Num
             (Num.num_of_bool
                (Interpreter.Eval_numeric.eval_relop op (to_value c1)
                   (to_value c2))))
    | _ -> (
        let (* dispatch *)
        open Interpreter in
        match op with
        | Values.I32 x -> i32_relop x s1 s2
        | Values.I64 x -> i64_relop x s1 s2
        | Values.F32 x -> f32_relop x s1 s2
        | Values.F64 x -> f64_relop x s1 s2)
  in
  s

let eval_cvtop (op : cvtop) (s : expr) : expr =
  let s =
    match s with
    | Val (Num c) ->
        Val
          (Num (of_value (Interpreter.Eval_numeric.eval_cvtop op (to_value c))))
    | _ -> (
        let (* dispatch cvtop func *)
        open Interpreter in
        match op with
        | Values.I32 x -> i32_cvtop x s
        | Values.I64 x -> i64_cvtop x s
        | Values.F32 x -> f32_cvtop x s
        | Values.F64 x -> f64_cvtop x s)
  in
  s
