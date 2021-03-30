open Z3
open Types
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

let bit0 = BitVector.mk_numeral ctx "0" 32
let bit1 = BitVector.mk_numeral ctx "1" 32

let get_sort (e : value_type) : Sort.sort =
  begin match e with
  | I32Type | F32Type -> bv32_sort
  | I64Type | F64Type -> bv64_sort
  end

let extend (e : Expr.expr) (sz : int) : Expr.expr =
  let sz' = BitVector.get_size (Expr.get_sort e) in
  if sz' < sz then BitVector.mk_zero_ext ctx (sz - sz') e else e

module Zi32 = 
struct
  open Si32

  let encode_value (i : int) : Expr.expr =
    Expr.mk_numeral_int ctx i bv32_sort

  let encode_unop (op : unop) (e : Expr.expr) : Expr.expr =
    failwith "Zi32: encode_unop: Construct not supported yet"

  let encode_binop (op : binop) (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let op' = begin match op with
      | I32Add  -> BitVector.mk_add  ctx
      | I32Sub  -> BitVector.mk_sub  ctx
      | I32Mul  -> BitVector.mk_mul  ctx
      | I32DivS -> BitVector.mk_sdiv ctx
      | I32DivU -> BitVector.mk_udiv ctx
      | I32And  -> BitVector.mk_and  ctx
      | I32Xor  -> BitVector.mk_xor  ctx
      | I32Or   -> BitVector.mk_or   ctx
      | I32Shl  -> BitVector.mk_shl  ctx
      | I32ShrS -> BitVector.mk_ashr ctx
      | I32ShrU -> BitVector.mk_lshr ctx
      end
    in op' e1 e2

  let encode_relop (op : relop) (e1 : Expr.expr) 
      (e2 : Expr.expr) : Expr.expr = 
    let e1' = extend e1 32
    and e2' = extend e2 32
    and op' = begin match op with
      | I32Eq  -> Boolean.mk_eq ctx
      | I32Ne  -> (fun x1 x2 -> Boolean.mk_not ctx (Boolean.mk_eq ctx x1 x2))
      | I32LtU -> BitVector.mk_ult ctx
      | I32LtS -> BitVector.mk_slt ctx
      | I32LeU -> BitVector.mk_ule ctx
      | I32LeS -> BitVector.mk_sle ctx
      | I32GtU -> BitVector.mk_ugt ctx
      | I32GtS -> BitVector.mk_sgt ctx
      | I32GeU -> BitVector.mk_uge ctx
      | I32GeS -> BitVector.mk_sge ctx
      end
    in Boolean.mk_ite ctx (op' e1' e2') bit1 bit0
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
    let op = begin match op with
      | I64Add  -> BitVector.mk_add  ctx
      | I64Sub  -> BitVector.mk_sub  ctx
      | I64Mul  -> BitVector.mk_mul  ctx
      | I64Div  -> BitVector.mk_sdiv ctx
      | I64And  -> BitVector.mk_and  ctx
      | I64Xor  -> BitVector.mk_xor  ctx
      | I64Or   -> BitVector.mk_or   ctx
      end
    in op e1 e2

  let encode_relop (op : relop) (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    (* Extend to fix these: (I64Eq, (I64Ne, x, y), 1) *)
    let e1' = extend e1 64
    and e2' = extend e2 64
    and op' = begin match op with
      | I64Eq  -> Boolean.mk_eq ctx
      | I64Ne  -> (fun x1 x2 -> Boolean.mk_not ctx (Boolean.mk_eq ctx x1 x2))
      | I64LtU -> BitVector.mk_ult ctx
      | I64LtS -> BitVector.mk_slt ctx
      | I64LeU -> BitVector.mk_ule ctx
      | I64LeS -> BitVector.mk_sle ctx
      | I64GtU -> BitVector.mk_ugt ctx
      | I64GtS -> BitVector.mk_sgt ctx
      | I64GeU -> BitVector.mk_uge ctx
      | I64GeS -> BitVector.mk_sge ctx
      end
    in Boolean.mk_ite ctx (op' e1' e2') bit1 bit0
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
    let op' =
      begin match op with
      | F32Neg -> FloatingPoint.mk_neg ctx
      end
    in op' (to_fp e)

  let encode_binop (op : binop) (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let e1' = to_fp e1
    and e2' = to_fp e2
    and op' = begin match op with
      | F32Add -> FloatingPoint.mk_add ctx rm
      | F32Sub -> FloatingPoint.mk_sub ctx rm
      | F32Mul -> FloatingPoint.mk_mul ctx rm
      | F32Div -> FloatingPoint.mk_div ctx rm
      end
    in op' e1' e2'

  let encode_relop (op : relop) (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let e1' = to_fp e1
    and e2' = to_fp e2
    and op' = begin match op with
      | F32Eq -> Boolean.mk_eq  ctx
      | F32Ne -> (fun x1 x2 -> Boolean.mk_not ctx (Boolean.mk_eq ctx x1 x2))
      | F32Lt -> FloatingPoint.mk_lt  ctx
      | F32Le -> FloatingPoint.mk_leq ctx
      | F32Gt -> FloatingPoint.mk_gt  ctx
      | F32Ge -> FloatingPoint.mk_geq ctx
      end
    in Boolean.mk_ite ctx (op' e1' e2') bit1 bit0
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
    let op'  = begin match op with
      | F64Neg -> FloatingPoint.mk_neg ctx
      end
    in op' (to_fp e)

  let encode_binop (op : binop) (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let e1' = to_fp e1
    and e2' = to_fp e2
    and op' = begin match op with
      | F64Add -> FloatingPoint.mk_add ctx rm
      | F64Sub -> FloatingPoint.mk_sub ctx rm
      | F64Mul -> FloatingPoint.mk_mul ctx rm
      | F64Div -> FloatingPoint.mk_div ctx rm
      end
    in op' e1' e2'

  let encode_relop (op : relop) (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let e1' = to_fp e1
    and e2' = to_fp e2
    and op' = begin match op with
      | F64Eq -> Boolean.mk_eq  ctx
      | F64Ne -> (fun x1 x2 -> Boolean.mk_not ctx (Boolean.mk_eq ctx x1 x2))
      | F64Lt -> FloatingPoint.mk_lt  ctx
      | F64Le -> FloatingPoint.mk_leq ctx
      | F64Gt -> FloatingPoint.mk_gt  ctx
      | F64Ge -> FloatingPoint.mk_geq ctx
      end
    in Boolean.mk_ite ctx (op' e1' e2') bit1 bit0
end

let encode_value (v : value) : Expr.expr =
  begin match v with
  | I32 i -> Zi32.encode_value (Int32.to_int i)
  | I64 i -> Zi64.encode_value (Int64.to_int i)
  | F32 f -> Zf32.encode_value (F32.to_float f)
  | F64 f -> Zf32.encode_value (F64.to_float f)
  end

let rec encode_sym_expr (e : sym_expr) : Expr.expr =
  begin match e with
  | Value v -> encode_value v
  | I32Unop  (op, e) ->
      let e' = encode_sym_expr e in
      Zi32.encode_unop op e'
  | I32Binop (op, e1, e2) ->
      let e1' = encode_sym_expr e1
      and e2' = encode_sym_expr e2 in
      Zi32.encode_binop op e1' e2'
  | I32Relop (op, e1, e2) ->
      let e1' = encode_sym_expr e1
      and e2' = encode_sym_expr e2 in
      Zi32.encode_relop op e1' e2'
  | I64Unop  (op, e) ->
      let e' = encode_sym_expr e in
      Zi64.encode_unop op e'
  | I64Binop (op, e1, e2) ->
      let e1' = encode_sym_expr e1
      and e2' = encode_sym_expr e2 in
      Zi64.encode_binop op e1' e2'
  | I64Relop (op, e1, e2) ->
      let e1' = encode_sym_expr e1
      and e2' = encode_sym_expr e2 in
      Zi64.encode_relop op e1' e2'
  | F32Unop (op, e) ->
      let e' = encode_sym_expr e in
      Zf32.encode_unop op e'
  | F32Binop (op, e1, e2) ->
      let e1' = encode_sym_expr e1
      and e2' = encode_sym_expr e2 in
      Zf32.encode_binop op e1' e2'
  | F32Relop (op, e1, e2) ->
      let e1' = encode_sym_expr e1
      and e2' = encode_sym_expr e2 in
      Zf32.encode_relop op e1' e2'
  | F64Unop (op, e) ->
      let e' = encode_sym_expr e in
      Zf64.encode_unop op e'
  | F64Binop (op, e1, e2) ->
      let e1' = encode_sym_expr e1
      and e2' = encode_sym_expr e2 in
      Zf64.encode_binop op e1' e2'
  | F64Relop (op, e1, e2) ->
      let e1' = encode_sym_expr e1
      and e2' = encode_sym_expr e2 in
      Zf64.encode_relop op e1' e2'
  | Symbolic (t, x) ->
      Expr.mk_const_s ctx x (get_sort (type_of_symbolic t))
  | Extract  (e, h, l) -> 
      let e' = encode_sym_expr e in
      (* UGLY HACK *)
      let e'' = 
        if FloatingPoint.is_fp e' then FloatingPoint.mk_to_ieee_bv ctx e' 
        else e'
      in
      BitVector.mk_extract ctx (h * 8 - 1) (l * 8) e''
  | Concat (e1, e2) -> 
      let e1' = encode_sym_expr e1
      and e2' = encode_sym_expr e2 in
      BitVector.mk_concat ctx e1' e2'
  | BoolOp (op, e1, e2) ->
      let e1' = encode_sym_expr e1
      and e2' = encode_sym_expr e2 in
      begin match op with
      | And -> BitVector.mk_and ctx e1' e2'
      | Or  -> BitVector.mk_or  ctx e1' e2'
      end
  end

let encode_top_level_expr (e : sym_expr) : Expr.expr =
  let encode_float_constraints (t : symbolic) (x : string) : Expr.expr list =
    begin match t with
    | SymFloat32 -> 
        let bv = Expr.mk_const_s ctx x bv32_sort in
        let fp = FloatingPoint.mk_to_fp_bv ctx bv fp32_sort in
        let c1 = Boolean.mk_not ctx (FloatingPoint.mk_is_nan ctx fp)
        and c2 = Boolean.mk_not ctx (FloatingPoint.mk_is_infinite ctx fp) in
        [c1; c2]
    | SymFloat64 ->
        let bv = Expr.mk_const_s ctx x bv64_sort in
        let fp = FloatingPoint.mk_to_fp_bv ctx bv fp64_sort in
        let c1 = Boolean.mk_not ctx (FloatingPoint.mk_is_nan ctx fp)
        and c2 = Boolean.mk_not ctx (FloatingPoint.mk_is_infinite ctx fp) in
        [c1; c2]
    | _ -> []
    end
  in
  let syms' = List.map (fun (x, t) -> encode_float_constraints t x) 
      (List.sort_uniq (fun (x1, _) (x2, _) -> String.compare x1 x2) (get_symbols e)) in
  Boolean.mk_and ctx ([encode_sym_expr e] @ (List.concat syms'))

let check_sat_core (pc : path_conditions) : Model.model option =
  assert (not (pc = []));
  let pc_as_bv = List.map encode_sym_expr pc in
  let pc' = List.map (fun c -> Boolean.mk_eq ctx c bit1) pc_as_bv in
  let solver = Solver.mk_solver ctx None in
  List.iter (fun c -> Solver.add solver [c]) pc';
  (*
  Printf.printf "\n\nDEBUG ASSERTIONS:\n";
  List.iter (fun a -> Printf.printf "%s\n" (Expr.to_string a)) 
            (Solver.get_assertions solver);
  *)
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
      if Expr.is_numeral n then begin
        let bytes_of_n = Bytes.of_string (Expr.to_string n) in
        Bytes.set bytes_of_n 0 '0';
        Some (Int64.of_string (Bytes.to_string bytes_of_n))
      end else None
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
