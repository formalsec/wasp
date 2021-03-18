open Z3
open Values
open Symvalue

let cfg = [
  ("model", "true");
  ("proof", "false");
  ("unsat_core", "false")
]

let ctx : context = mk_context cfg

let bv32_sort = BitVector.mk_sort ctx 32
let bv64_sort = BitVector.mk_sort ctx 64
let fp32_sort = FloatingPoint.mk_sort_single ctx
let fp64_sort = FloatingPoint.mk_sort_double ctx

let rm = FloatingPoint.RoundingMode.mk_round_nearest_ties_to_even ctx

module Zi32 = 
struct
  open Si32

  let encode_value (i : int) : Expr.expr =
    Expr.mk_numeral_int ctx i bv32_sort

  let encode_unop (op : unop) (e : Expr.expr) : Expr.expr =
    failwith "Zi32: encode_unop: Construct not supported yet"

  let encode_binop (op : binop) (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    begin match op with
    | I32Add  -> BitVector.mk_add  ctx e1 e2
    | I32Sub  -> BitVector.mk_sub  ctx e1 e2
    | I32Mul  -> BitVector.mk_mul  ctx e1 e2
    | I32DivS -> BitVector.mk_sdiv ctx e1 e2
    | I32DivU -> BitVector.mk_udiv ctx e1 e2
    | I32And  -> BitVector.mk_and  ctx e1 e2
    | I32Xor  -> BitVector.mk_xor  ctx e1 e2
    | I32Or   -> BitVector.mk_or   ctx e1 e2
    | I32Shl  -> BitVector.mk_shl  ctx e1 e2
    | I32ShrS -> BitVector.mk_ashr ctx e1 e2
    | I32ShrU -> BitVector.mk_lshr ctx e1 e2
    end

  let encode_relop (op : relop) (e1 : Expr.expr) 
      (e2 : Expr.expr) : Expr.expr = 
    begin match op with
    | I32Eq   -> Boolean.mk_eq ctx e1 e2
    | I32Neq  -> Boolean.mk_not ctx (Boolean.mk_eq ctx e1 e2) 
    | I32Lt   -> BitVector.mk_slt ctx e1 e2
    | I32LtEq -> BitVector.mk_sle ctx e1 e2
    | I32Gt   -> BitVector.mk_sgt ctx e1 e2
    | I32GtEq -> BitVector.mk_sge ctx e1 e2
    end
end

module Zi64 =
struct
  open Si64

  let encode_value (i : int) : Expr.expr =
    Expr.mk_numeral_int ctx i bv64_sort

  let encode_unop (op : unop) (e : Expr.expr) : Expr.expr =
    failwith "Zi64: encode_unop: Construct not supported yet"

  let encode_binop (op : binop) (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    begin match op with
    | I64Add  -> BitVector.mk_add  ctx e1 e2
    | I64Sub  -> BitVector.mk_sub  ctx e1 e2
    | I64Mul  -> BitVector.mk_mul  ctx e1 e2
    | I64Div  -> BitVector.mk_sdiv ctx e1 e2
    | I64And  -> BitVector.mk_and  ctx e1 e2
    | I64Xor  -> BitVector.mk_xor  ctx e1 e2
    | I64Or   -> BitVector.mk_or   ctx e1 e2
    end

  let encode_relop (op : relop) (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    begin match op with
    | I64Eq   -> Boolean.mk_eq ctx e1 e2
    | I64Neq  -> Boolean.mk_not ctx (Boolean.mk_eq ctx e1 e2)
    | I64Lt   -> BitVector.mk_slt ctx e1 e2
    | I64LtEq -> BitVector.mk_sle ctx e1 e2
    | I64Gt   -> BitVector.mk_sgt ctx e1 e2
    | I64GtEq -> BitVector.mk_sge ctx e1 e2
    end
end

module Zf32 =
struct
  open Sf32

  let to_fp (e : Expr.expr) : Expr.expr =
    if BitVector.is_bv e then
      FloatingPoint.mk_to_fp_bv ctx e fp32_sort
    else e

  let encode_value (f : float) : Expr.expr =
    FloatingPoint.mk_numeral_f ctx f fp32_sort

  let encode_unop (op : unop) (e : Expr.expr) : Expr.expr =
    begin match op with
    | F32Neg -> FloatingPoint.mk_neg ctx (to_fp e)
    end

  let encode_binop (op : binop) (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let e1' = to_fp e1 in
    let e2' = to_fp e2 in
    begin match op with
    | F32Add -> FloatingPoint.mk_add ctx rm e1' e2'
    | F32Sub -> FloatingPoint.mk_sub ctx rm e1' e2'
    | F32Mul -> FloatingPoint.mk_mul ctx rm e1' e2'
    | F32Div -> FloatingPoint.mk_div ctx rm e1' e2'
    end

  let encode_relop (op : relop) (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let e1' = to_fp e1 in
    let e2' = to_fp e2 in
    begin match op with
    | F32Eq   -> Boolean.mk_eq  ctx e1' e2'
    | F32Neq  -> Boolean.mk_not ctx (Boolean.mk_eq ctx e1' e2')
    | F32Lt   -> FloatingPoint.mk_lt  ctx e1' e2'
    | F32LtEq -> FloatingPoint.mk_leq ctx e1' e2'
    | F32Gt   -> FloatingPoint.mk_gt  ctx e1' e2'
    | F32GtEq -> FloatingPoint.mk_geq ctx e1' e2'
    end
end

module Zf64 =
struct
  open Sf64

  let to_fp (e : Expr.expr) : Expr.expr =
    if BitVector.is_bv e then
      FloatingPoint.mk_to_fp_bv ctx e fp64_sort
    else e

  let encode_value (f : float) : Expr.expr =
    FloatingPoint.mk_numeral_f ctx f fp64_sort

  let encode_unop (op : unop) (e : Expr.expr) : Expr.expr =
    begin match op with
    | F64Neg -> FloatingPoint.mk_neg ctx (to_fp e)
    end

  let encode_binop (op : binop) (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let e1' = to_fp e1 in
    let e2' = to_fp e2 in
    begin match op with
    | F64Add -> FloatingPoint.mk_add ctx rm e1' e2'
    | F64Sub -> FloatingPoint.mk_sub ctx rm e1' e2'
    | F64Mul -> FloatingPoint.mk_mul ctx rm e1' e2'
    | F64Div -> FloatingPoint.mk_div ctx rm e1' e2'
    end

  let encode_relop (op : relop) (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let e1' = to_fp e1 in
    let e2' = to_fp e2 in
    begin match op with
    | F64Eq   -> Boolean.mk_eq  ctx e1' e2'
    | F64Neq  -> Boolean.mk_not ctx (Boolean.mk_eq ctx e1' e2')
    | F64Lt   -> FloatingPoint.mk_lt  ctx e1' e2'
    | F64LtEq -> FloatingPoint.mk_leq ctx e1' e2'
    | F64Gt   -> FloatingPoint.mk_gt  ctx e1' e2'
    | F64GtEq -> FloatingPoint.mk_geq ctx e1' e2'
    end
end

let rec encode_sym_expr (e : sym_expr) : Expr.expr =
  begin match e with
  | Value v ->
      begin match v with
      | I32 i -> Zi32.encode_value (Int32.to_int i)
      | I64 i -> Zi64.encode_value (Int64.to_int i)
      | F32 f -> Zf32.encode_value (F32.to_float f)
      | F64 f -> Zf64.encode_value (F64.to_float f)
      end
  | I32Unop  (op, e) ->
      let e' = encode_sym_expr e in
      Zi32.encode_unop op e'
  | I32Binop (op, e1, e2) ->
      let e1' = encode_sym_expr e1 in
      let e2' = encode_sym_expr e2 in
      Zi32.encode_binop op e1' e2'
  | I32Relop (op, e1, e2) ->
      let e1' = encode_sym_expr e1 in
      let e2' = encode_sym_expr e2 in
      Zi32.encode_relop op e1' e2'
  | I64Unop  (op, e) ->
      let e' = encode_sym_expr e in
      Zi64.encode_unop op e'
  | I64Binop (op, e1, e2) ->
      let e1' = encode_sym_expr e1 in
      let e2' = encode_sym_expr e2 in
      Zi64.encode_binop op e1' e2'
  | I64Relop (op, e1, e2) ->
      let e1' = encode_sym_expr e1 in
      let e2' = encode_sym_expr e2 in
      Zi64.encode_relop op e1' e2'
  | F32Unop (op, e) ->
      let e' = encode_sym_expr e in
      Zf32.encode_unop op e'
  | F32Binop (op, e1, e2) ->
      let e1' = encode_sym_expr e1 in
      let e2' = encode_sym_expr e2 in
      Zf32.encode_binop op e1' e2'
  | F32Relop (op, e1, e2) ->
      let e1' = encode_sym_expr e1 in
      let e2' = encode_sym_expr e2 in
      Zf32.encode_relop op e1' e2'
  | F64Unop (op, e) ->
      let e' = encode_sym_expr e in
      Zf64.encode_unop op e'
  | F64Binop (op, e1, e2) ->
      let e1' = encode_sym_expr e1 in
      let e2' = encode_sym_expr e2 in
      Zf64.encode_binop op e1' e2'
  | F64Relop (op, e1, e2) ->
      let e1' = encode_sym_expr e1 in
      let e2' = encode_sym_expr e2 in
      Zf64.encode_relop op e1' e2'
  | Symbolic (t, x) ->
      Expr.mk_const_s ctx x (BitVector.mk_sort ctx (Symvalue.size t))
  | Extract  (e, i) -> 
      let e' = encode_sym_expr e in
      (* UGLY HACK *)
      let e'' = 
        if FloatingPoint.is_fp e' then FloatingPoint.mk_to_ieee_bv ctx e' 
        else e'
      in
      BitVector.mk_extract ctx (i * 8 + 7) (i * 8) e''
  | Concat (e1, e2) -> 
      let e1' = encode_sym_expr e1 in
      let e2' = encode_sym_expr e2 in
      BitVector.mk_concat ctx e1' e2'
  | BoolOp (op, e1, e2) ->
      let e1' = encode_sym_expr e1 in
      let e2' = encode_sym_expr e2 in
      begin match op with
      | And -> Boolean.mk_and ctx [e1'; e2']
      | Or  -> Boolean.mk_or  ctx [e1'; e2']
      end
  end

let encode_top_level_expr (e : sym_expr) : Expr.expr =
  let encode_float_constraints (t : symbolic) (x : string) : Expr.expr list =
    begin match t with
    | SymFloat32 -> 
        let bv = Expr.mk_const_s ctx x bv32_sort in
        let fp = FloatingPoint.mk_to_fp_bv ctx bv fp32_sort in
        let c1 = Boolean.mk_not ctx (FloatingPoint.mk_is_nan ctx fp) in
        let c2 = Boolean.mk_not ctx (FloatingPoint.mk_is_infinite ctx fp) in
        [c1; c2]
    | SymFloat64 ->
        let bv = Expr.mk_const_s ctx x bv64_sort in
        let fp = FloatingPoint.mk_to_fp_bv ctx bv fp64_sort in
        let c1 = Boolean.mk_not ctx (FloatingPoint.mk_is_nan ctx fp) in
        let c2 = Boolean.mk_not ctx (FloatingPoint.mk_is_infinite ctx fp) in
        [c1; c2]
    | _ -> []
    end
  in
  let syms' = List.map (fun (x, t) -> encode_float_constraints t x) 
      (List.sort_uniq (fun (x1, _) (x2, _) -> String.compare x1 x2) (get_symbols e)) in
  Boolean.mk_and ctx ([encode_sym_expr e] @ (List.concat syms'))

let check_sat_core (pc : path_conditions) : Model.model option =
  assert (not (pc = []));
  let pc' = List.map encode_top_level_expr pc in
  let solver = Solver.mk_solver ctx None in
  List.iter (fun c -> Solver.add solver [c]) pc';
  Printf.printf "\n\nDEBUG ASSERTIONS:\n";
  List.iter (fun a -> Printf.printf "%s\n" (Expr.to_string a)) 
            (Solver.get_assertions solver);

  begin match Solver.check solver [] with
  | Solver.UNSATISFIABLE -> None
  | Solver.UNKNOWN       -> failwith ("unknown: " ^ (Solver.get_reason_unknown solver)) (* fail? *)
  | Solver.SATISFIABLE   -> Solver.get_model solver
  end

let lift_z3_model (model : Model.model) (sym_int32 : string list)
    (sym_int64 : string list) (sym_float32 : string list)
    (sym_float64 : string list) : Logicenv.logical_env = 

  let lift_z3_const (c : sym_expr) : int64 option =
    let recover_numeral (n : Expr.expr) : int64 option =
      if Expr.is_numeral n then (
        let str_n = Bytes.of_string (Expr.to_string n) in 
        Bytes.set str_n 0 '0';
        Some (Int64.of_string (Bytes.to_string str_n))
      ) else None
    in
    let v = Model.get_const_interp_e model (encode_sym_expr c) in
    Option.map_default recover_numeral None v
  in
  let store = Logicenv.create_logic_env [] in
  List.iter (fun x ->
    let n = lift_z3_const (Symbolic (SymInt32, x)) in
    let v = Option.map (fun y -> I32 (Int64.to_int32 y)) n in
    Option.map_default (Logicenv.set_sym store x) () v
  ) sym_int32;
  List.iter (fun x ->
    let n = lift_z3_const (Symbolic (SymInt64, x)) in
    let v = Option.map (fun y -> I64 y) n in
    Option.map_default (Logicenv.set_sym store x) () v
  ) sym_int64;
  List.iter (fun x ->
    let n = lift_z3_const (Symbolic (SymFloat32, x)) in
    let v = Option.map (fun y -> F32 (F32.of_bits (Int64.to_int32 y))) n in
    Option.map_default (Logicenv.set_sym store x) () v
  ) sym_float32;
  List.iter (fun x ->
    let n = lift_z3_const (Symbolic (SymFloat64, x)) in
    let v = Option.map (fun y -> F64 (F64.of_bits y)) n in
    Option.map_default (Logicenv.set_sym store x) () v
  ) sym_float64;
  store
