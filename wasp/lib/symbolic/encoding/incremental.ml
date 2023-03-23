open Z3
open Interpreter
open Interpreter.Types
open Interpreter.Values

exception Unknown

let time_solver = ref 0.0

let time_call f acc =
  let start = Sys.time () in
  let ret = f () in
  acc := !acc +. ((Sys.time ()) -. start);
  ret

type s = Solver.solver
type t = {
  solver : s;
  pc : Expression.path_conditions ref;
}

let ctx =
  Z3.mk_context
    [ ("model", "true"); ("proof", "false"); ("unsat_core", "false") ]

(* Sorts *)
let bv32_sort = BitVector.mk_sort ctx 32
let bv64_sort = BitVector.mk_sort ctx 64
let fp32_sort = FloatingPoint.mk_sort_single ctx
let fp64_sort = FloatingPoint.mk_sort_double ctx

(* Rounding Modes *)
let rne = FloatingPoint.RoundingMode.mk_rne ctx
let rtz = FloatingPoint.RoundingMode.mk_rtz ctx

(* Match WASM Type with Z3 Sort *)
let get_sort (e : Types.value_type) : Z3.Sort.sort =
  begin match e with
  | Types.I32Type -> bv32_sort
  | Types.I64Type -> bv64_sort
  | Types.F32Type -> fp32_sort
  | Types.F64Type -> fp64_sort
  end

(* Bool helper - cast bool to bv *)
let encode_bool (to_bv : bool) (cond : Expr.expr) : Expr.expr =
  let bv_true  = BitVector.mk_numeral ctx "1" 32
  and bv_false = BitVector.mk_numeral ctx "0" 32 in
  if to_bv then Boolean.mk_ite ctx cond bv_true bv_false
           else cond

module Zi32 =
struct
  open Expression.I32

  let encode_value (i : int) : Expr.expr =
    Expr.mk_numeral_int ctx i bv32_sort

  let encode_unop (op : unop) (e : Expr.expr) : Expr.expr =
    failwith "Zi32: encode_unop: Construct not supported yet"

  let encode_binop
      (op : binop)
      (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let op' = match op with
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
      | I32RemS -> BitVector.mk_srem ctx
      | I32RemU -> BitVector.mk_urem ctx
    in op' e1 e2

  let encode_relop
      ?(to_bv=false)
      (op : relop)
      (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let op' = match op with
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
    in encode_bool to_bv (op' e1 e2)

  let encode_cvtop (op : cvtop) (e : Expr.expr) : Expr.expr =
    let op' = match op with
      | I32TruncSF32 -> (fun f -> FloatingPoint.mk_to_sbv ctx rtz f 32)
      | I32TruncUF32 -> (fun f -> FloatingPoint.mk_to_ubv ctx rtz f 32)
      | I32TruncSF64 -> (fun f -> FloatingPoint.mk_to_sbv ctx rtz f 32)
      | I32TruncUF64 -> (fun f -> FloatingPoint.mk_to_ubv ctx rtz f 32)
      | I32ReinterpretFloat -> FloatingPoint.mk_to_ieee_bv ctx
    in op' e
end

module Zi64 =
struct
  open Expression.I64

  let encode_value (i : int) : Expr.expr =
    Expr.mk_numeral_int ctx i bv64_sort

  let encode_unop (op : unop) (e : Expr.expr) : Expr.expr =
    failwith "Zi64: encode_unop: Construct not supported yet"

  let encode_binop
      (op : binop)
      (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let op' = match op with
      | I64Add  -> BitVector.mk_add  ctx
      | I64Sub  -> BitVector.mk_sub  ctx
      | I64Mul  -> BitVector.mk_mul  ctx
      | I64DivS -> BitVector.mk_sdiv ctx
      | I64DivU -> BitVector.mk_udiv ctx
      | I64And  -> BitVector.mk_and  ctx
      | I64Xor  -> BitVector.mk_xor  ctx
      | I64Or   -> BitVector.mk_or   ctx
      | I64Shl  -> BitVector.mk_shl  ctx
      | I64ShrS -> BitVector.mk_ashr ctx
      | I64ShrU -> BitVector.mk_lshr ctx
      | I64RemS -> BitVector.mk_srem ctx
      | I64RemU -> BitVector.mk_urem ctx
    in op' e1 e2

  let encode_relop
      ?(to_bv=false)
      (op : relop)
      (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let op' = match op with
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
    in encode_bool to_bv (op' e1 e2)

  let encode_cvtop (op : cvtop) (e : Expr.expr) : Expr.expr =
    let op' = match op with
      | I64ExtendSI32 -> BitVector.mk_sign_ext ctx 32
      | I64ExtendUI32 -> BitVector.mk_zero_ext ctx 32
      (* rounding towards zero (aka truncation) *)
      | I64TruncSF32 -> (fun f -> FloatingPoint.mk_to_sbv ctx rtz f 64)
      | I64TruncUF32 -> (fun f -> FloatingPoint.mk_to_ubv ctx rtz f 64)
      | I64TruncSF64 -> (fun f -> FloatingPoint.mk_to_sbv ctx rtz f 64)
      | I64TruncUF64 -> (fun f -> FloatingPoint.mk_to_ubv ctx rtz f 64)
      | I64ReinterpretFloat -> FloatingPoint.mk_to_ieee_bv ctx
    in op' e
end

module Zf32 =
struct
  open Expression.F32

  let encode_value (f : float) : Expr.expr =
    FloatingPoint.mk_numeral_f ctx f fp32_sort

  let encode_unop (op : unop) (e : Expr.expr) : Expr.expr =
    let op' = match op with
      | F32Neg -> FloatingPoint.mk_neg ctx
      | F32Abs -> FloatingPoint.mk_abs ctx
      | F32Sqrt -> FloatingPoint.mk_sqrt ctx rne
      | F32Nearest -> FloatingPoint.mk_round_to_integral ctx rne
    in op' e

  let encode_binop
      (op : binop)
      (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let op' = match op with
      | F32Add -> FloatingPoint.mk_add ctx rne
      | F32Sub -> FloatingPoint.mk_sub ctx rne
      | F32Mul -> FloatingPoint.mk_mul ctx rne
      | F32Div -> FloatingPoint.mk_div ctx rne
      | F32Min -> FloatingPoint.mk_min ctx
      | F32Max -> FloatingPoint.mk_max ctx
    in op' e1 e2

  let encode_relop
      ?(to_bv=false)
      (op : relop)
      (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let op' = match op with
      | F32Eq -> FloatingPoint.mk_eq  ctx
      | F32Ne -> (fun x1 x2 -> Boolean.mk_not ctx (FloatingPoint.mk_eq ctx x1 x2))
      | F32Lt -> FloatingPoint.mk_lt  ctx
      | F32Le -> FloatingPoint.mk_leq ctx
      | F32Gt -> FloatingPoint.mk_gt  ctx
      | F32Ge -> FloatingPoint.mk_geq ctx
    in encode_bool to_bv (op' e1 e2)

  let encode_cvtop (op : cvtop) (e : Expr.expr) : Expr.expr =
    let op' = match op with
      | F32DemoteF64 ->
          (fun bv -> FloatingPoint.mk_to_fp_float    ctx rne bv fp32_sort)
      | F32ConvertSI32 ->
          (fun bv -> FloatingPoint.mk_to_fp_signed   ctx rne bv fp32_sort)
      | F32ConvertUI32 ->
          (fun bv -> FloatingPoint.mk_to_fp_unsigned ctx rne bv fp32_sort)
      | F32ConvertSI64 ->
          (fun bv -> FloatingPoint.mk_to_fp_signed   ctx rne bv fp32_sort)
      | F32ConvertUI64 ->
          (fun bv -> FloatingPoint.mk_to_fp_unsigned ctx rne bv fp32_sort)
      | F32ReinterpretInt ->
          (fun bv -> FloatingPoint.mk_to_fp_bv ctx bv fp32_sort)
    in op' e
end

module Zf64 =
struct
  open Expression.F64

  let encode_value (f : float) : Expr.expr =
    FloatingPoint.mk_numeral_f ctx f fp64_sort

  let encode_unop (op : unop) (e : Expr.expr) : Expr.expr =
    let op'  = match op with
      | F64Neg -> FloatingPoint.mk_neg ctx
      | F64Abs -> FloatingPoint.mk_abs ctx
      | F64Sqrt -> FloatingPoint.mk_sqrt ctx rne
      | F64Nearest -> FloatingPoint.mk_round_to_integral ctx rne
    in op' e

  let encode_binop
      (op : binop)
      (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let op' = match op with
      | F64Add -> FloatingPoint.mk_add ctx rne
      | F64Sub -> FloatingPoint.mk_sub ctx rne
      | F64Mul -> FloatingPoint.mk_mul ctx rne
      | F64Div -> FloatingPoint.mk_div ctx rne
      | F64Min -> FloatingPoint.mk_min ctx
      | F64Max -> FloatingPoint.mk_max ctx
    in op' e1 e2

  let encode_relop
      ?(to_bv=false)
      (op : relop)
      (e1 : Expr.expr)
      (e2 : Expr.expr) : Expr.expr =
    let op' = match op with
      | F64Eq -> FloatingPoint.mk_eq  ctx
      | F64Ne -> (fun x1 x2 -> Boolean.mk_not ctx (FloatingPoint.mk_eq ctx x1 x2))
      | F64Lt -> FloatingPoint.mk_lt  ctx
      | F64Le -> FloatingPoint.mk_leq ctx
      | F64Gt -> FloatingPoint.mk_gt  ctx
      | F64Ge -> FloatingPoint.mk_geq ctx
    in encode_bool to_bv (op' e1 e2)

  let encode_cvtop (op : cvtop) (e : Expr.expr) : Expr.expr =
    let op' = match op with
      | F64PromoteF32 ->
          (fun bv -> FloatingPoint.mk_to_fp_float    ctx rne bv fp64_sort)
      | F64ConvertSI32 ->
          (fun bv -> FloatingPoint.mk_to_fp_signed   ctx rne bv fp64_sort)
      | F64ConvertUI32 ->
          (fun bv -> FloatingPoint.mk_to_fp_unsigned ctx rne bv fp64_sort)
      | F64ConvertSI64 ->
          (fun bv -> FloatingPoint.mk_to_fp_signed   ctx rne bv fp64_sort)
      | F64ConvertUI64 ->
          (fun bv -> FloatingPoint.mk_to_fp_unsigned ctx rne bv fp64_sort)
      | F64ReinterpretInt ->
          (fun bv -> FloatingPoint.mk_to_fp_bv ctx bv fp64_sort)
    in op' e

end

let encode_value (v : Values.value) : Z3.Expr.expr =
  match v with
  | Values.I32 i -> Zi32.encode_value (Int32.to_int i)
  | Values.I64 i -> Zi64.encode_value (Int64.to_int i)
  | Values.F32 f -> Zf32.encode_value (F32.to_float f)
  | Values.F64 f -> Zf64.encode_value (F64.to_float f)

let rec encode_sym_expr ?(bool_to_bv=false) (e : Expression.t) : Expr.expr =
  let open Expression in
  let open Values in
  match e with
  | Value v -> encode_value v
  | SymPtr (base, offset) ->
      let base' = encode_value (I32 base) in
      let offset' = encode_sym_expr offset in
      Zi32.encode_binop Expression.I32.I32Add base' offset'
  | I32Unop  (op, e) ->
      let e' = encode_sym_expr e in
      Zi32.encode_unop op e'
  | I32Binop (op, e1, e2) ->
      let e1' = encode_sym_expr ~bool_to_bv:true e1
      and e2' = encode_sym_expr ~bool_to_bv:true e2 in
      Zi32.encode_binop op e1' e2'
  | I32Relop (op, e1, e2) ->
      let e1' = encode_sym_expr ~bool_to_bv:true e1
      and e2' = encode_sym_expr ~bool_to_bv:true e2 in
      Zi32.encode_relop ~to_bv:bool_to_bv op e1' e2'
  | I32Cvtop (op, e) ->
      let e' = encode_sym_expr e in
      Zi32.encode_cvtop op e'
  | I64Unop  (op, e) ->
      let e' = encode_sym_expr e in
      Zi64.encode_unop op e'
  | I64Binop (op, e1, e2) ->
      let e1' = encode_sym_expr ~bool_to_bv:true e1
      and e2' = encode_sym_expr ~bool_to_bv:true e2 in
      Zi64.encode_binop op e1' e2'
  | I64Relop (op, e1, e2) ->
      let e1' = encode_sym_expr ~bool_to_bv:true e1
      and e2' = encode_sym_expr ~bool_to_bv:true e2 in
      Zi64.encode_relop ~to_bv:bool_to_bv op e1' e2'
  | I64Cvtop (op, e) ->
      let e' = encode_sym_expr e in
      Zi64.encode_cvtop op e'
  | F32Unop (op, e) ->
      let e' = encode_sym_expr e in
      Zf32.encode_unop op e'
  | F32Binop (op, e1, e2) ->
      let e1' = encode_sym_expr e1 and e2' = encode_sym_expr e2 in
      Zf32.encode_binop op e1' e2'
  | F32Relop (op, e1, e2) ->
      let e1' = encode_sym_expr e1 and e2' = encode_sym_expr e2 in
      Zf32.encode_relop ~to_bv:bool_to_bv op e1' e2'
  | F32Cvtop (op, e) ->
      let e' = encode_sym_expr e in
      Zf32.encode_cvtop op e'
  | F64Unop (op, e) ->
      let e' = encode_sym_expr e in
      Zf64.encode_unop op e'
  | F64Binop (op, e1, e2) ->
      let e1' = encode_sym_expr e1 and e2' = encode_sym_expr e2 in
      Zf64.encode_binop op e1' e2'
  | F64Relop (op, e1, e2) ->
      let e1' = encode_sym_expr e1 and e2' = encode_sym_expr e2 in
      Zf64.encode_relop ~to_bv:bool_to_bv op e1' e2'
  | F64Cvtop (op, e) ->
      let e' = encode_sym_expr e in
      Zf64.encode_cvtop op e'
  | Symbolic (t, x) ->
      Expr.mk_const_s ctx x (get_sort (type_of_symbolic t))
  | Extract  (e, h, l) ->
      let e' = encode_sym_expr ~bool_to_bv:true e in
      BitVector.mk_extract ctx (h * 8 - 1) (l * 8) e'
  | Concat (e1, e2) ->
      let e1' = encode_sym_expr e1 and e2' = encode_sym_expr e2 in
      BitVector.mk_concat ctx e1' e2'

let rec encode_formula (a : Formula.t) : Expr.expr =
  let open Formula in
  match a with
  | True    -> Boolean.mk_true ctx
  | False   -> Boolean.mk_false ctx
  | Relop e -> encode_sym_expr e
  | Not c   -> Boolean.mk_not ctx (encode_formula c)
  | And (c1, c2) ->
      let c1' = encode_formula c1
      and c2' = encode_formula c2 in
      Boolean.mk_and ctx [c1'; c2']
  | Or (c1, c2) ->
      let c1' = encode_formula c1
      and c2' = encode_formula c2 in
      Boolean.mk_or ctx [c1'; c2']

let create () : t =
  {
    solver = Solver.mk_solver ctx None;
    pc = ref [];
  }

let clone (e : t) : t =
  { solver = Solver.translate e.solver ctx; pc = ref !(e.pc) }

let add (e : t) (c : Expression.t):  unit =
  e.pc := c :: !(e.pc);
  let ec = encode_sym_expr ~bool_to_bv:false c in
  Solver.add e.solver [ec]

let check (e : t) (vs : Expression.t list) : bool =
  let vs' = List.map (encode_sym_expr ~bool_to_bv:false) vs in
  let b =
    let sat =
      time_call (fun () -> Solver.check e.solver vs') time_solver
    in
    match sat with
    | Solver.SATISFIABLE -> true
    | Solver.UNKNOWN ->
      failwith ("unknown: " ^ (Solver.get_reason_unknown e.solver)) (* fail? *)
    | Solver.UNSATISFIABLE -> false
  in
  b

let fork (e : t) (co : Expression.t) : bool * bool =
  let negated_co = Expression.negate_relop co in
  (check e [ co ]), (check e [ negated_co ])

let set (s : string) (i : int) (n : char) =
  let bs = Bytes.of_string s in
  Bytes.set bs i n;
  Bytes.to_string bs

let int64_of_bv (bv : Expr.expr) : int64 =
  assert (Expr.is_numeral bv);
  Int64.of_string (set (Expr.to_string bv) 0 '0')

let int64_of_fp (fp : Expr.expr) (ebits : int) (sbits : int) : int64 =
  assert (Expr.is_numeral fp);
  if FloatingPoint.is_numeral_nan ctx fp then
    if FloatingPoint.is_numeral_negative ctx fp then
      if sbits = 23 then Int64.of_int32 0xffc0_0000l
      else 0xfff8_0000_0000_0000L
    else
      if sbits = 23 then Int64.of_int32 0x7fc0_0000l
      else 0x7ff8_0000_0000_0000L
  else if FloatingPoint.is_numeral_inf ctx fp then
    if FloatingPoint.is_numeral_negative ctx fp then
      if sbits = 23 then (Int64.of_int32 (Int32.bits_of_float (-. (1.0 /. 0.0))))
      else Int64.bits_of_float (-. (1.0 /. 0.0))
    else
      if sbits = 23 then (Int64.of_int32 (Int32.bits_of_float (1.0 /. 0.0)))
      else Int64.bits_of_float (1.0 /. 0.0)
  else if FloatingPoint.is_numeral_zero ctx fp then
    if FloatingPoint.is_numeral_negative ctx fp then
      if sbits = 23 then (Int64.of_int32 0x8000_0000l)
      else 0x8000_0000_0000_0000L
    else
      if sbits = 23 then (Int64.of_int32 (Int32.bits_of_float 0.0))
      else Int64.bits_of_float 0.0
  else
    let fp = Expr.to_string fp in
    let fp = String.sub fp 4 ((String.length fp) - 5) in
    let fp_list = List.map (fun fp -> set fp 0 '0')
                           (String.split_on_char ' ' fp) in
    let bit_list = List.map (fun fp -> Int64.of_string fp) fp_list in
    let sign     = Int64.shift_left (List.nth bit_list 0) (ebits + sbits)
    and exponent = Int64.shift_left (List.nth bit_list 1) (sbits)
    and fraction = List.nth bit_list 2 in
    Int64.(logor sign (logor exponent fraction))

let value_of_const model c =
  let interp = Model.get_const_interp_e model (encode_sym_expr c) in
  let f e =
    let v =
      if BitVector.is_bv e then int64_of_bv e
      else
        let ebits = FloatingPoint.get_ebits ctx (Expr.get_sort e)
        and sbits = FloatingPoint.get_sbits ctx (Expr.get_sort e) in
        int64_of_fp e ebits (sbits - 1)
    in
    match Expression.type_of c with
    | I32Type -> I32 (Int64.to_int32 v)
    | I64Type -> I64 v
    | F32Type -> F32 (F32.of_bits (Int64.to_int32 v))
    | F64Type -> F64 (F64.of_bits v)
  in
  Option.map f interp

(** fails if solver isn't currently SAT *)
let model (e : t) : Model.model =
  assert (check e []);
  Option.get (Solver.get_model e.solver)

(** fails if solver isn't currently SAT *)
let value_binds (e : t) vars : (string * value) list =
  let m = model e in
  List.fold_left
    (fun a (x, t) ->
      let v = value_of_const m (Expression.to_symbolic t x) in
      Batteries.Option.map_default (fun v' -> (x, v') :: a) (a) v)
    [] vars

(** fails if solver isn't currently SAT *)
let string_binds (e : t) vars :
    (string * string * string) list =
  let m = model e in
  List.map
    (fun const ->
      let sort = Sort.to_string (FuncDecl.get_range const)
      and name = Symbol.to_string (FuncDecl.get_name const)
      and interp =
        Batteries.Option.map_default Expr.to_string ""
          (Model.get_const_interp m const)
      in
      (sort, name, interp))
    (Model.get_const_decls m)
