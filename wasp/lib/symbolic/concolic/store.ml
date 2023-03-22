open Common
open Syntax.I32
open Syntax.I64
open Syntax.F32
open Syntax.F64
open Syntax.Val
open Interpreter
open Interpreter.Types
open Interpreter.Values

type name = string
type bind = name * value

type store = {
  sym : Counter.t;
  ord : name BatDynArray.t;
  map : (name, value) Hashtbl.t;
}

type t = store

let reset (s : t) : unit =
  Counter.clear s.sym;
  Hashtbl.clear s.map;
  BatDynArray.clear s.ord

let clear (s : t) : unit = Hashtbl.clear s.map

let init (s : t) (binds : bind list) : unit =
  List.iter (fun (k, v) -> Hashtbl.add s.map k v) binds

let create (binds : bind list) : t =
  let s =
    {
      sym = Counter.create ();
      ord = BatDynArray.create ();
      map = Hashtbl.create Flags.hashtbl_default_size;
    }
  in
  init s binds;
  s

let add (s : t) (x : name) (v : value) : unit =
  BatDynArray.add s.ord x;
  Hashtbl.replace s.map x v

let find (s : t) (x : name) : value = Hashtbl.find s.map x
let find_opt (s : t) (x : name) : value option = Hashtbl.find_opt s.map x
let exists (s : t) (x : name) : bool = BatDynArray.mem x s.ord

let get (s : t) (x : name) (ty : value_type) (b : bool) : value =
  let v =
    match find_opt s x with
    | Some v -> v
    | None -> (
        match ty with
        | I32Type -> I32 (I32.rand (if b then 2 else 127))
        | I64Type -> I64 (I64.rand 127)
        | F32Type -> F32 (F32.rand 127.0)
        | F64Type -> F64 (F64.rand 127.0))
  in
  add s x v;
  v

let next (s : t) (x : name) : name =
  let id = Counter.get_and_inc s.sym x in
  if id = 0 then x else x ^ "_" ^ string_of_int id

let is_empty (s : t) : bool = 0 = Hashtbl.length s.map

let update (s : t) (binds : bind list) : unit =
  List.iter (fun (x, v) -> Hashtbl.replace s.map x v) binds

let to_json (s : t) : string =
  let jsonify_bind (b : bind) : string =
    let n, v = b in
    "{" ^ "\"name\" : \"" ^ n ^ "\", " ^ "\"value\" : \"" ^ pp_string_of_value v
    ^ "\", " ^ "\"type\" : \""
    ^ string_of_value_type (Values.type_of v)
    ^ "\"" ^ "}"
  in
  "["
  ^ String.concat ","
      (BatDynArray.fold_left
         (fun a x -> jsonify_bind (x, find s x) :: a)
         [] s.ord)
  ^ "]"

let strings_to_json string_env : string =
  let jsonify_bind b : string =
    let t, x, v = b in
    "{" ^ "\"name\" : \"" ^ x ^ "\", " ^ "\"value\" : \"" ^ v ^ "\", "
    ^ "\"type\" : \"" ^ t ^ "\"" ^ "}"
  in
  "[" ^ String.concat ", " (List.map jsonify_bind string_env) ^ "]"

let to_string (s : t) : string =
  BatDynArray.fold_left
    (fun a k ->
      let v = find s k in
      a ^ "(" ^ k ^ "->" ^ string_of_value v ^ ")\n")
    "" s.ord

let get_key_types (s : t) : (string * value_type) list =
  Hashtbl.fold (fun k v acc -> (k, Values.type_of v) :: acc) s.map []

let to_expr (s : t) : sym_expr list =
  Hashtbl.fold
    (fun k v acc ->
      let e =
        match v with
        | I32 _ -> I32Relop (Syntax.I32.I32Eq, Symbolic (SymInt32, k), Value v)
        | I64 _ -> I64Relop (Syntax.I64.I64Eq, Symbolic (SymInt64, k), Value v)
        | F32 _ -> F32Relop (Syntax.F32.F32Eq, Symbolic (SymFloat32, k), Value v)
        | F64 _ -> F64Relop (Syntax.F64.F64Eq, Symbolic (SymFloat64, k), Value v)
      in
      e :: acc)
    s.map []

let rec eval (env : t) (e : sym_expr) : value =
  match simplify e with
  | SymPtr (b, o) ->
      let b = I32 b in
      Eval_numeric.eval_binop (I32 Ast.I32Op.Add) b (eval env o)
  | Value v -> v
  | I32Binop (op, e1, e2) ->
      let v1 = eval env e1
      and v2 = eval env e2
      and op' =
        match op with
        | I32Add -> I32 Ast.I32Op.Add
        | I32Sub -> I32 Ast.I32Op.Sub
        | I32Mul -> I32 Ast.I32Op.Mul
        | I32Shl -> I32 Ast.I32Op.Shl
        | I32DivU -> I32 Ast.I32Op.DivU
        | I32DivS -> I32 Ast.I32Op.DivS
        | I32RemU -> I32 Ast.I32Op.RemU
        | I32RemS -> I32 Ast.I32Op.RemS
        | I32ShrU -> I32 Ast.I32Op.ShrU
        | I32ShrS -> I32 Ast.I32Op.ShrS
        | I32And -> I32 Ast.I32Op.And
        | I32Or -> I32 Ast.I32Op.Or
        | I32Xor -> I32 Ast.I32Op.Xor
      in
      Eval_numeric.eval_binop op' v1 v2
  | I32Unop (op, e') ->
      let v = eval env e'
      and op' = match op with I32Clz -> I32 Ast.I32Op.Clz in
      Eval_numeric.eval_unop op' v
  | I32Relop (op, e1, e2) ->
      let v1 = eval env e1
      and v2 = eval env e2
      and op' =
        match op with
        | I32Eq -> I32 Ast.I32Op.Eq
        | I32Ne -> I32 Ast.I32Op.Ne
        | I32LtU -> I32 Ast.I32Op.LtU
        | I32GtU -> I32 Ast.I32Op.GtU
        | I32LtS -> I32 Ast.I32Op.LtS
        | I32GtS -> I32 Ast.I32Op.GtS
        | I32LeU -> I32 Ast.I32Op.LeU
        | I32GeU -> I32 Ast.I32Op.GeU
        | I32LeS -> I32 Ast.I32Op.LeS
        | I32GeS -> I32 Ast.I32Op.GeS
      in
      value_of_bool (Eval_numeric.eval_relop op' v1 v2)
  | I32Cvtop (op, e') ->
      let v = eval env e'
      and op' =
        match op with
        | I32TruncSF32 -> I32 Ast.I32Op.TruncSF32
        | I32TruncUF32 -> I32 Ast.I32Op.TruncUF32
        | I32TruncSF64 -> I32 Ast.I32Op.TruncSF64
        | I32TruncUF64 -> I32 Ast.I32Op.TruncUF64
        | I32ReinterpretFloat -> I32 Ast.I32Op.ReinterpretFloat
      in
      Eval_numeric.eval_cvtop op' v
  | I64Binop (op, e1, e2) ->
      let v1 = eval env e1
      and v2 = eval env e2
      and op' =
        match op with
        | I64Add -> I64 Ast.I64Op.Add
        | I64Sub -> I64 Ast.I64Op.Sub
        | I64Mul -> I64 Ast.I64Op.Mul
        | I64Shl -> I64 Ast.I64Op.Shl
        | I64DivU -> I64 Ast.I64Op.DivU
        | I64DivS -> I64 Ast.I64Op.DivS
        | I64RemU -> I64 Ast.I64Op.RemU
        | I64RemS -> I64 Ast.I64Op.RemS
        | I64ShrU -> I64 Ast.I64Op.ShrU
        | I64ShrS -> I64 Ast.I64Op.ShrS
        | I64And -> I64 Ast.I64Op.And
        | I64Or -> I64 Ast.I64Op.Or
        | I64Xor -> I64 Ast.I64Op.Xor
      in
      Eval_numeric.eval_binop op' v1 v2
  | I64Unop (op, e') ->
      let v = eval env e'
      and op' = match op with I64Clz -> I64 Ast.I64Op.Clz in
      Eval_numeric.eval_unop op' v
  | I64Relop (op, e1, e2) ->
      let v1 = eval env e1
      and v2 = eval env e2
      and op' =
        match op with
        | I64Eq -> I64 Ast.I64Op.Eq
        | I64Ne -> I64 Ast.I64Op.Ne
        | I64LtU -> I64 Ast.I64Op.LtU
        | I64GtU -> I64 Ast.I64Op.GtU
        | I64LtS -> I64 Ast.I64Op.LtS
        | I64GtS -> I64 Ast.I64Op.GtS
        | I64LeU -> I64 Ast.I64Op.LeU
        | I64GeU -> I64 Ast.I64Op.GeU
        | I64LeS -> I64 Ast.I64Op.LeS
        | I64GeS -> I64 Ast.I64Op.GeS
      in
      value_of_bool (Eval_numeric.eval_relop op' v1 v2)
  | I64Cvtop (op, e') ->
      let v = eval env e'
      and op' =
        match op with
        | I64ExtendSI32 -> I64 Ast.I64Op.ExtendSI32
        | I64ExtendUI32 -> I64 Ast.I64Op.ExtendUI32
        | I64TruncSF32 -> I64 Ast.I64Op.TruncSF32
        | I64TruncUF32 -> I64 Ast.I64Op.TruncUF32
        | I64TruncSF64 -> I64 Ast.I64Op.TruncSF64
        | I64TruncUF64 -> I64 Ast.I64Op.TruncUF64
        | I64ReinterpretFloat -> I64 Ast.I64Op.ReinterpretFloat
      in
      Eval_numeric.eval_cvtop op' v
  | F32Binop (op, e1, e2) ->
      let v1 = eval env e1
      and v2 = eval env e2
      and op' =
        match op with
        | F32Add -> F32 Ast.F32Op.Add
        | F32Sub -> F32 Ast.F32Op.Sub
        | F32Mul -> F32 Ast.F32Op.Mul
        | F32Div -> F32 Ast.F32Op.Div
        | F32Min -> F32 Ast.F32Op.Min
        | F32Max -> F32 Ast.F32Op.Max
      in
      Eval_numeric.eval_binop op' v1 v2
  | F32Unop (op, e') ->
      let v = eval env e'
      and op' =
        match op with
        | F32Neg -> F32 Ast.F32Op.Neg
        | F32Abs -> F32 Ast.F32Op.Abs
        | F32Sqrt -> F32 Ast.F32Op.Sqrt
        | F32Nearest -> F32 Ast.F32Op.Nearest
      in
      Eval_numeric.eval_unop op' v
  | F32Relop (op, e1, e2) ->
      let v1 = eval env e1
      and v2 = eval env e2
      and op' =
        match op with
        | F32Eq -> F32 Ast.F32Op.Eq
        | F32Ne -> F32 Ast.F32Op.Ne
        | F32Lt -> F32 Ast.F32Op.Lt
        | F32Gt -> F32 Ast.F32Op.Gt
        | F32Le -> F32 Ast.F32Op.Le
        | F32Ge -> F32 Ast.F32Op.Ge
      in
      value_of_bool (Eval_numeric.eval_relop op' v1 v2)
  | F32Cvtop (op, e') ->
      let v = eval env e'
      and op' =
        match op with
        | F32DemoteF64 -> F32 Ast.F32Op.DemoteF64
        | F32ConvertSI32 -> F32 Ast.F32Op.ConvertSI32
        | F32ConvertUI32 -> F32 Ast.F32Op.ConvertUI32
        | F32ConvertSI64 -> F32 Ast.F32Op.ConvertSI64
        | F32ConvertUI64 -> F32 Ast.F32Op.ConvertUI64
        | F32ReinterpretInt -> F32 Ast.F32Op.ReinterpretInt
      in
      Eval_numeric.eval_cvtop op' v
  | F64Binop (op, e1, e2) ->
      let v1 = eval env e1
      and v2 = eval env e2
      and op' =
        match op with
        | F64Add -> F64 Ast.F64Op.Add
        | F64Sub -> F64 Ast.F64Op.Sub
        | F64Mul -> F64 Ast.F64Op.Mul
        | F64Div -> F64 Ast.F64Op.Div
        | F64Min -> F64 Ast.F64Op.Min
        | F64Max -> F64 Ast.F64Op.Max
      in
      Eval_numeric.eval_binop op' v1 v2
  | F64Unop (op, e') ->
      let v = eval env e'
      and op' =
        match op with
        | F64Neg -> F64 Ast.F64Op.Neg
        | F64Abs -> F64 Ast.F64Op.Abs
        | F64Sqrt -> F64 Ast.F64Op.Sqrt
        | F64Nearest -> F64 Ast.F64Op.Nearest
      in
      Eval_numeric.eval_unop op' v
  | F64Relop (op, e1, e2) ->
      let v1 = eval env e1
      and v2 = eval env e2
      and op' =
        match op with
        | F64Eq -> F64 Ast.F64Op.Eq
        | F64Ne -> F64 Ast.F64Op.Ne
        | F64Lt -> F64 Ast.F64Op.Lt
        | F64Gt -> F64 Ast.F64Op.Gt
        | F64Le -> F64 Ast.F64Op.Le
        | F64Ge -> F64 Ast.F64Op.Ge
      in
      value_of_bool (Eval_numeric.eval_relop op' v1 v2)
  | F64Cvtop (op, e') ->
      let v = eval env e'
      and op' =
        match op with
        | F64PromoteF32 -> F64 Ast.F64Op.PromoteF32
        | F64ConvertSI32 -> F64 Ast.F64Op.ConvertSI32
        | F64ConvertUI32 -> F64 Ast.F64Op.ConvertUI32
        | F64ConvertSI64 -> F64 Ast.F64Op.ConvertSI64
        | F64ConvertUI64 -> F64 Ast.F64Op.ConvertUI64
        | F64ReinterpretInt -> F64 Ast.F64Op.ReinterpretInt
      in
      Eval_numeric.eval_cvtop op' v
  | Symbolic (ty, var) -> find env var
  | Extract (e', h, l) ->
      let v =
        match eval env e' with
        | I32 x -> Int64.of_int32 x
        | I64 x -> x
        | F32 x -> Int64.of_int32 (F32.to_bits x)
        | F64 x -> F64.to_bits x
      in
      I64 (nland64 (Int64.shift_right v (l * 8)) (h - l))
  | Concat (e1, e2) -> eval env (simplify (Concat (e1, e2)))
