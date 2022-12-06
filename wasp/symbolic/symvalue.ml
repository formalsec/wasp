open Si32
open Types
open Values

type symbolic = SymInt8 | SymInt16 | SymInt32 | SymInt64 |
                SymFloat32 | SymFloat64

type sym_expr =
  (* Value *)
  | Value    of value
  | Ptr      of value
  (* I32 operations *)
  | I32Binop of Si32.binop * sym_expr * sym_expr
  | I32Unop  of Si32.unop  * sym_expr
  | I32Relop of Si32.relop * sym_expr * sym_expr
  | I32Cvtop of Si32.cvtop * sym_expr
  (* I64 operations *)
  | I64Binop of Si64.binop * sym_expr * sym_expr
  | I64Unop  of Si64.unop  * sym_expr
  | I64Relop of Si64.relop * sym_expr * sym_expr
  | I64Cvtop of Si64.cvtop * sym_expr
  (* F32 operations *)
  | F32Binop of Sf32.binop * sym_expr * sym_expr
  | F32Unop  of Sf32.unop  * sym_expr
  | F32Relop of Sf32.relop * sym_expr * sym_expr
  | F32Cvtop of Sf32.cvtop * sym_expr
  (* F64 operations *)
  | F64Binop of Sf64.binop * sym_expr * sym_expr
  | F64Unop  of Sf64.unop  * sym_expr
  | F64Relop of Sf64.relop * sym_expr * sym_expr
  | F64Cvtop of Sf64.cvtop * sym_expr
  (* Symbolic *)
  | Symbolic of symbolic * string
  (* Encoding Auxiliary *)
  | Extract  of sym_expr * int * int
  | Concat   of sym_expr * sym_expr

(*  Pair ( (concrete) Value, (symbolic) Expression)  *)
type sym_value = value * sym_expr

(*  To keep record of the path conditions  *)
type path_conditions = sym_expr list

let type_of_symbolic = function
  | SymInt8    -> I32Type
  | SymInt16   -> I32Type
  | SymInt32   -> I32Type
  | SymInt64   -> I64Type
  | SymFloat32 -> F32Type
  | SymFloat64 -> F64Type

let to_symbolic (t : value_type) (x : string) : sym_expr =
  let symb = match t with
    | I32Type -> SymInt32
    | I64Type -> SymInt64
    | F32Type -> SymFloat32
    | F64Type -> SymFloat64
  in Symbolic (symb, x)


let negate_relop (e : sym_expr) : sym_expr =
  match e with
  (* Relop *)
  | I32Relop (op, e1, e2) -> I32Relop (Si32.neg_relop op, e1, e2)
  | I64Relop (op, e1, e2) -> I64Relop (Si64.neg_relop op, e1, e2)
  | F32Relop (op, e1, e2) -> F32Relop (Sf32.neg_relop op, e1, e2)
  | F64Relop (op, e1, e2) -> F64Relop (Sf64.neg_relop op, e1, e2)
  | _ -> failwith "Not a relop"

(* Measure complexity of formulas *)
let rec length (e : sym_expr) : int =
  begin match e with
  | Value v -> 1
  | Ptr p   -> 1
	(* I32 *)
	| I32Unop  (op, e)      -> 1 + (length e)
	| I32Binop (op, e1, e2) -> 1 + (length e1) + (length e2)
	| I32Relop (op, e1, e2) -> 1 + (length e1) + (length e2)
  | I32Cvtop (op, e)      -> 1 + (length e)
	(* I64 *)
	| I64Unop  (op, e)      -> 1 + (length e)
	| I64Binop (op, e1, e2) -> 1 + (length e1) + (length e2)
	| I64Relop (op, e1, e2) -> 1 + (length e1) + (length e2)
  | I64Cvtop (op, e)      -> 1 + (length e)
	(* F32 *)
	| F32Unop  (op, e)      -> 1 + (length e)
	| F32Binop (op, e1, e2) -> 1 + (length e1) + (length e2)
	| F32Relop (op, e1, e2) -> 1 + (length e1) + (length e2)
  | F32Cvtop (op, e)      -> 1 + (length e)
	(* F64 *)
	| F64Unop  (op, e)      -> 1 + (length e)
	| F64Binop (op, e1, e2) -> 1 + (length e1) + (length e2)
	| F64Relop (op, e1, e2) -> 1 + (length e1) + (length e2)
  | F64Cvtop (op, e)      -> 1 + (length e)
  (* Symbol *)
	| Symbolic (s, x)       -> 1
  | Extract  (e, _, _)    -> 1 + (length e)
  | Concat   (e1, e2)     -> 1 + (length e1) + (length e2)
  end

(*  Retrieves the symbolic variables  *)
let rec get_symbols (e : sym_expr) : (string * symbolic) list =
	begin match e with
  (* Value - holds no symbols *)
	| Value _ -> []
  | Ptr _   -> []
  (* I32 *)
  | I32Unop  (op, e1)     -> (get_symbols e1)
  | I32Binop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  | I32Relop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  | I32Cvtop (op, e)      -> (get_symbols e)
  (* I64 *)
  | I64Unop  (op, e1)     -> (get_symbols e1)
  | I64Binop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  | I64Relop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  | I64Cvtop (op, e)      -> (get_symbols e)
  (* F32 *)
  | F32Unop  (op, e1)     -> (get_symbols e1)
  | F32Binop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  | F32Relop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  | F32Cvtop (op, e)      -> (get_symbols e)
  (* F64 *)
  | F64Unop  (op, e1)     -> (get_symbols e1)
  | F64Binop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  | F64Relop (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  | F64Cvtop (op, e)      -> (get_symbols e)
  (* Symbol *)
  | Symbolic (t, x)       -> [(x, t)]
  | Extract  (e, _, _)    -> (get_symbols e)
  | Concat   (e1, e2)     -> (get_symbols e1) @ (get_symbols e2)
  end

(*  String representation of an symbolic types  *)
let string_of_symbolic (op : symbolic) : string =
  begin match op with
  | SymInt8    -> "SymInt8"
  | SymInt16   -> "SymInt16"
	| SymInt32   -> "SymInt32"
	| SymInt64   -> "SymInt64"
	| SymFloat32 -> "SymFloat32"
	| SymFloat64 -> "SymFloat64"
  end

(*  String representation of a sym_expr  *)
let rec to_string (e : sym_expr) : string =
	begin match e with
  | Value v ->
      string_of_value v
  | Ptr p ->
      let str_p = string_of_value p in
      "(Ptr " ^ str_p ^ ")"
	(* I32 *)
  | I32Unop  (op, e) ->
      let str_e = to_string e
      and str_op = Si32.string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | I32Binop (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = Si32.string_of_binop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | I32Relop  (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = Si32.string_of_relop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | I32Cvtop (op, e) ->
      let str_e = to_string e
      and str_op = Si32.string_of_cvtop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
	(* I64 *)
  | I64Unop  (op, e) ->
      let str_e = to_string e
      and str_op = Si64.string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | I64Binop (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = Si64.string_of_binop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | I64Relop (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = Si64.string_of_relop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | I64Cvtop (op, e) ->
      let str_e = to_string e
      and str_op = Si64.string_of_cvtop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
	(* F32 *)
  | F32Unop  (op, e) ->
      let str_e = to_string e
      and str_op = Sf32.string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | F32Binop (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = Sf32.string_of_binop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | F32Relop (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = Sf32.string_of_relop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | F32Cvtop (op, e) ->
      let str_e = to_string e
      and str_op = Sf32.string_of_cvtop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  (* F64 *)
  | F64Unop  (op, e) ->
      let str_e = to_string e
      and str_op = Sf64.string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | F64Binop (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = Sf64.string_of_binop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | F64Relop (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = Sf64.string_of_relop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | F64Cvtop (op, e) ->
      let str_e = to_string e
      and str_op = Sf64.string_of_cvtop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
	(* Symbolic *)
  | Symbolic (s, x) ->
      let str_s = string_of_symbolic s in
      "(" ^ str_s ^ " #" ^ x ^ ")"
  | Extract (e, h, l) ->
      let str_l = string_of_int l
      and str_h = string_of_int h
      and str_e = to_string e in
      "(Extract " ^ str_e ^ ", " ^ str_h ^ " " ^ str_l ^ ")"
  | Concat (e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2 in
      "(Concat " ^ str_e1 ^ " " ^ str_e2 ^ ")"
  end

let rec pp_to_string (e : sym_expr) : string =
	begin match e with
  | Value v ->
      Values.string_of_value v
  | Ptr p ->
      let str_p = string_of_value p in
      "(Ptr " ^ str_p ^ ")"
  (* I32 *)
  | I32Unop  (op, e) ->
      let str_e = pp_to_string e
      and str_op = Si32.pp_string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | I32Binop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = Si32.pp_string_of_binop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
 | I32Relop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = Si32.pp_string_of_relop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | I32Cvtop (op, e) ->
      let str_e = pp_to_string e
      and str_op = Si32.pp_string_of_cvtop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  (* I64 *)
  | I64Unop  (op, e) ->
      let str_e = pp_to_string e
      and str_op = Si64.pp_string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | I64Binop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = Si64.pp_string_of_binop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | I64Relop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = Si64.pp_string_of_relop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | I64Cvtop (op, e) ->
      let str_e = pp_to_string e
      and str_op = Si64.pp_string_of_cvtop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  (* F32 *)
  | F32Unop  (op, e) ->
      let str_e = pp_to_string e
      and str_op = Sf32.pp_string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | F32Binop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = Sf32.pp_string_of_binop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | F32Relop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = Sf32.pp_string_of_relop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | F32Cvtop (op, e) ->
      let str_e = pp_to_string e
      and str_op = Sf32.pp_string_of_cvtop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  (* F64 *)
  | F64Unop  (op, e) ->
      let str_e = pp_to_string e
      and str_op = Sf64.pp_string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | F64Binop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = Sf64.pp_string_of_binop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | F64Relop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = Sf64.pp_string_of_relop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | F64Cvtop (op, e) ->
      let str_e = pp_to_string e
      and str_op = Sf64.pp_string_of_cvtop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | Symbolic (s, x) -> "#" ^ x
  | Extract (e, h, l) ->
      let str_l = string_of_int l
      and str_h = string_of_int h
      and str_e = pp_to_string e in
      str_e ^ "[" ^ str_l ^ ":" ^ str_h ^ "]"
  | Concat (e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2 in
      "(" ^ str_e1 ^ " + " ^ str_e2 ^ ")"
  end

(*  String representation of a list of path conditions  *)
let string_of_pc (pc : path_conditions) : string =
  List.fold_left (fun acc c -> acc ^ (pp_to_string c) ^ ";\n  ") "" pc

let pp_string_of_pc (pc : path_conditions) : string =
  List.fold_left (fun acc e -> acc ^ (pp_to_string e) ^ ";  ") "" pc

let string_of_sym_value (el : sym_value list) : string =
  List.fold_left (
    fun acc (v, s) ->
      acc ^ (Values.string_of_value v) ^ ", " ^ (pp_to_string s) ^ "\n"
  ) "" el

let rec type_of (e : sym_expr) : value_type  =
  let rec concat_length (e' : sym_expr) : int =
    begin match e' with
    | Value v    -> Types.size (Values.type_of v)
    | Ptr _      -> 4
    | I32Unop  _ -> 4
    | I32Binop _ -> 4
    | I32Relop _ -> 4
    | I32Cvtop _ -> 4
    | I64Unop  _ -> 8
    | I64Binop _ -> 8
    | I64Relop _ -> 8
    | I64Cvtop _ -> 8
    | F32Unop  _ -> 4
    | F32Binop _ -> 4
    | F32Relop _ -> 4
    | F32Cvtop _ -> 4
    | F64Unop  _ -> 8
    | F64Binop _ -> 8
    | F64Relop _ -> 8
    | F64Cvtop _ -> 8
    | Symbolic (e'', _) ->
        (match e'' with
        | SymInt8 -> 1
        | SymInt16 -> 2
        | SymInt32 -> 4
        | SymInt64 -> 8
        | SymFloat32 -> 4
        | SymFloat64 -> 8)
    | Concat (e1, e2) -> (concat_length e1) + (concat_length e2)
    | Extract (_, h, l) -> h - l
    end
  in
  begin match e with
  | Value v    -> Values.type_of v
  | Ptr _      -> I32Type
  | I32Unop  _ -> I32Type
  | I32Binop _ -> I32Type
  | I32Relop _ -> I32Type
  | I32Cvtop _ -> I32Type
  | I64Unop  _ -> I64Type
  | I64Binop _ -> I64Type
  | I64Relop _ -> I64Type
  | I64Cvtop _ -> I64Type
  | F32Unop  _ -> F32Type
  | F32Binop _ -> F32Type
  | F32Relop _ -> F32Type
  | F32Cvtop _ -> F32Type
  | F64Unop  _ -> F64Type
  | F64Binop _ -> F64Type
  | F64Relop _ -> F64Type
  | F64Cvtop _ -> F64Type
  | Symbolic (e, _)    -> type_of_symbolic e
  | Extract  (e, _, _) -> type_of e
  | Concat (e1, e2) ->
    let len = concat_length (Concat (e1, e2)) in
    let len = if len < 4 then (Types.size (type_of e1)) + (Types.size (type_of e2))
                         else len
    in
    begin match len with
    | 4 -> I32Type
    | 8 -> I64Type
    | _ -> failwith "unsupported type length"
    end
  end



let rec get_ptr (e : sym_expr) : value option =
  (* FIXME: this function can be "simplified" *)
  begin match e with
  | Ptr p   -> Some p
  | Value _ -> None
  | I32Unop (_, e) -> get_ptr e
  | I32Binop (_, e1, e2) ->
      let p1 = get_ptr e1 in
      if Option.is_some p1 then p1 else get_ptr e2
  | I32Relop (_, e1, e2) ->
      let p1 = get_ptr e1 in
      if Option.is_some p1 then p1 else get_ptr e2
  | I32Cvtop (_, e) -> get_ptr e
  | I64Unop (_, e) -> get_ptr e
  | I64Binop (_, e1, e2) ->
      let p1 = get_ptr e1 in
      if Option.is_some p1 then p1 else get_ptr e2
  | I64Relop (_, e1, e2) ->
      let p1 = get_ptr e1 in
      if Option.is_some p1 then p1 else get_ptr e2
  | I64Cvtop (_, e) -> get_ptr e
  | F32Unop (_, e) -> get_ptr e
  | F32Binop (_, e1, e2) ->
      let p1 = get_ptr e1 in
      if Option.is_some p1 then p1 else get_ptr e2
  | F32Relop (_, e1, e2) ->
      let p1 = get_ptr e1 in
      if Option.is_some p1 then p1 else get_ptr e2
  | F32Cvtop (_, e) -> get_ptr e
  | F64Unop (_, e) -> get_ptr e
  | F64Binop (_, e1, e2) ->
      let p1 = get_ptr e1 in
      if Option.is_some p1 then p1 else get_ptr e2
  | F64Relop (_, e1, e2) ->
      let p1 = get_ptr e1 in
      if Option.is_some p1 then p1 else get_ptr e2
  | F64Cvtop (_, e) -> get_ptr e
  | Symbolic _ -> None
  | Extract (e, _, _) -> get_ptr e
  | Concat (e1, e2) ->
      (* assume concatenation of only one ptr *)
      let p1 = get_ptr e1 in
      if Option.is_some p1 then p1 else get_ptr e2
  end

let is_value (e : sym_expr) : bool =
  match e with Value _ -> true | _ -> false

let is_concrete (e : sym_expr) : bool =
  match e with Value _ | Ptr _ -> true | _ -> false

let is_relop (e : sym_expr) : bool =
  match e with
  | I32Relop _ | I64Relop _ | F32Relop _ | F64Relop _ -> true
  | _ -> false

let to_constraint (e : sym_expr) : sym_expr option =
  if is_concrete e then None
  else if is_relop e then Some e
  else Some (I32Relop (I32Ne, e, Value (I32 0l)))

let i32binop_to_astop (op : Si32.binop) =
  match op with
	| I32Add  -> Ast.I32Op.Add
	| I32And  -> Ast.I32Op.And
	| I32Or   -> Ast.I32Op.Or
	| I32Sub  -> Ast.I32Op.Sub
	| I32DivS -> Ast.I32Op.DivS
  | I32DivU -> Ast.I32Op.DivU
	| I32Xor  -> Ast.I32Op.Xor
	| I32Mul  -> Ast.I32Op.Mul
  | I32Shl  -> Ast.I32Op.Shl
  | I32ShrS -> Ast.I32Op.ShrS
  | I32ShrU -> Ast.I32Op.ShrU
  | I32RemS -> Ast.I32Op.RemS
  | I32RemU -> Ast.I32Op.RemU

let i32relop_to_astop (op : Si32.relop) =
  match op with
  | I32Eq  -> Ast.I32Op.Eq
  | I32Ne  -> Ast.I32Op.Ne
  | I32LtU -> Ast.I32Op.LtU
  | I32GtU -> Ast.I32Op.GtU
  | I32LtS -> Ast.I32Op.LtS
  | I32GtS -> Ast.I32Op.GtS
  | I32LeU -> Ast.I32Op.LeU
  | I32GeU -> Ast.I32Op.GeU
  | I32LeS -> Ast.I32Op.LeS
  | I32GeS -> Ast.I32Op.GeS

let nland x n =
  let rec loop x' n' acc =
    if n' = 0 then Int64.logand x' acc
    else loop x' (n' - 1) Int64.(logor (shift_left acc 8) 0xffL)
  in loop x n 0L

let rec new_simplify ?(extract = true) (e : sym_expr)  : sym_expr =
  begin match e with
  | Value v -> Value v
  | Ptr v   -> Ptr v
  | I32Binop (op, e1, e2) ->
      let e1' = new_simplify e1
      and e2' = new_simplify e2 in
      begin match e1', e2' with
      | Value (I32 0l), _ ->
        begin match op with
        | I32Add | I32Or   | I32Sub  -> e2'
        | I32And | I32DivS | I32DivU
        | I32Mul | I32RemS | I32RemU -> Value (I32 0l)
        | _ -> I32Binop (op, e1', e2')
        end

      | _, Value (I32 0l) ->
        begin match op with
        | I32Add | I32Or | I32Sub -> e1'
        | I32And | I32Mul -> Value (I32 0l)
        | _ -> I32Binop (op, e1', e2')
        end

      | Value v1, Value v2 ->
        Value (Eval_numeric.eval_binop (I32 (i32binop_to_astop op)) v1 v2)

      | I32Binop (op2, x, Value v1), Value v2 when not (is_value x) ->
        begin match op, op2 with
        | I32Add, I32Add ->
          let v = Eval_numeric.eval_binop (I32 Ast.I32Op.Add) v1 v2 in
          I32Binop (I32Add, x, Value v)
        | I32Add, I32Sub
        | I32Sub, I32Add ->
          let v = Eval_numeric.eval_binop (I32 Ast.I32Op.Sub) v1 v2 in
          I32Binop (I32Add, x, Value v)
        | I32Sub, I32Sub ->
          let v = Eval_numeric.eval_binop (I32 Ast.I32Op.Add) v1 v2 in
          I32Binop (I32Sub, x, Value v)
        | _, _ -> I32Binop (op, e1', e2')
        end

      | bop, Value (I32 1l)
      | Value (I32 1l), bop when (is_relop bop) && (op = I32And) -> bop

      | _ -> I32Binop (op, e1', e2')
      end

  | I32Relop (op, e1, e2) ->
    let e1' = new_simplify e1
    and e2' = new_simplify e2 in
    begin match e1', e2' with
    | Value v1, Value v2 | Ptr   v1, Value v2
    | Value v1, Ptr   v2 | Ptr   v1, Ptr   v2 ->
      let op' = I32 (i32relop_to_astop op) in
      let ret = Eval_numeric.eval_relop op' v1 v2 in
      Value (Values.value_of_bool ret)

    | _ -> I32Relop (op, e1', e2')
    end

  | Extract (s, h, l) when extract = false -> e

  | Extract (s, h, l) when extract = true ->
    begin match s with
    | Ptr (I64 p) ->
      let p' = nland Int64.(shift_right p (l * 8)) (h - l) in
      Ptr (I64  p')
    | Value (I64 x) ->
      let x' = nland (Int64.shift_right x (l * 8)) (h - l) in
      Value (I64 x')
    | _ when (h - l) = (Types.size (type_of s)) -> s
    | _ -> e
    end

  | Concat (e1, e2) ->
    let e1' = new_simplify ~extract:false e1
    and e2' = new_simplify ~extract:false e2 in
    begin match e1', e2' with
    | Extract (Ptr (I64 p2), h2, l2), Extract (Ptr (I64 p1), h1, l1) ->
      let d1 = (h1 - l1) and d2 = (h2 - l2) in
      let p1' = nland (Int64.shift_right p1 (l1 * 8)) d1
      and p2' = nland (Int64.shift_right p2 (l2 * 8)) d2 in
      let p = Int64.(logor (shift_left p2' (d1 * 8)) p1') in
      Extract (Ptr (I64 p), d1 + d2, 0)

    | Extract (Value (I64 x2), h2, l2), Extract (Value (I64 x1), h1, l1) ->
      let d1 = (h1 - l1) and d2 = (h2 - l2) in
      let x1' = nland (Int64.shift_right x1 (l1 * 8)) d1
      and x2' = nland (Int64.shift_right x2 (l2 * 8)) d2 in
      let x = Int64.(logor (shift_left x2' (d1 * 8)) x1') in
      Extract (Value (I64 x), d1 + d2, 0)

    | Extract (s1, h, m1), Extract (s2, m2, l) when (s1 = s2) && (m1 = m2) ->
      Extract (s1, h, l)

    | Extract (Value (I64 x2), h2, l2),
    Concat (Extract (Value (I64 x1), h1, l1), se) when not (is_value se) ->
      let d1 = (h1 - l1) and d2 = (h2 - l2) in
      let x1' = nland (Int64.shift_right x1 (l1 * 8)) d1
      and x2' = nland (Int64.shift_right x2 (l2 * 8)) d2 in
      let x = Int64.(logor (shift_left x2' (d1 * 8)) x1') in
      Concat (Extract (Value (I64 x), d1 + d2, 0), se)

    | _ -> Concat (e1', e2')
    end
  | _ -> e
  end

let rec rec_simplify (e : sym_expr) : sym_expr =
  match e with
  | Value v -> Value v
  | I32Binop (op, e1, e2) ->
      let e1' = rec_simplify e1
      and e2' = rec_simplify e2 in
      begin match op with
      | I32Add ->
        begin match e1', e2' with
        | Value v1, Value v2 ->
            Value (Eval_numeric.eval_binop (I32 Ast.I32Op.Add) v1 v2)

        | I32Binop (I32Add, e1'', Value (I32 v1)), Value (I32 v2) ->
            I32Binop (I32Add, e1'', Value (I32 (Int32.add v1 v2)))

        | I32Binop (I32Add, Symbolic (t, x), Value v1), Value v2 ->
            let v : sym_expr = Value (Eval_numeric.eval_binop (I32 Ast.I32Op.Add) v1 v2) in
            I32Binop (I32Add, Symbolic (t, x), v)

        | I32Binop (I32Sub, Symbolic (t, x), Value v1), Value v2 ->
            let v : sym_expr = Value (Eval_numeric.eval_binop (I32 Ast.I32Op.Sub) v1 v2) in
            I32Binop (I32Add, Symbolic (t, x), v)

        | _ -> I32Binop (I32Add, e1', e2')
        end
      | I32Sub  ->
          begin match e1', e2' with
          | Value v1, Value v2 ->
              Value (Eval_numeric.eval_binop (I32 Ast.I32Op.Sub) v1 v2)
          | I32Binop (I32Add, Symbolic (t, x), Value v1), Value v2 ->
              let v : sym_expr = Value (Eval_numeric.eval_binop (I32 Ast.I32Op.Sub) v1 v2) in
              I32Binop (I32Add, Symbolic (t, x), v)
          | I32Binop (I32Sub, Symbolic (t, x), Value v1), Value v2 ->
              let v : sym_expr = Value (Eval_numeric.eval_binop (I32 Ast.I32Op.Add) v1 v2) in
              I32Binop (I32Sub, Symbolic (t, x), v)
          | _ -> I32Binop (I32Sub , e1', e2')
          end
      | I32Mul  -> I32Binop (I32Mul , e1', e2')
      | I32DivS -> I32Binop (I32DivS, e1', e2')
      | I32DivU -> I32Binop (I32DivU, e1', e2')
      | I32And  -> (match e1', e2' with
        | Value v1, Value v2 ->
            Value (Eval_numeric.eval_binop (I32 Ast.I32Op.And) v1 v2)
        | Value (I32 0l), _
        | _, Value (I32 0l) -> Value (I32 0l)
        | Value (I32 1l), I32Relop (op', r1, r2) ->
          I32Relop (op', r1, r2)
        | I32Relop (op', r1, r2), Value (I32 1l) ->
          I32Relop (op', r1, r2)
        | I64Relop (op', r1, r2), Value (I32 1l) ->
          I64Relop (op', r1, r2)
        | I32Binop (I32And, e3, Value v1), Value v2 when v1 = v2 -> e1'
        | _, _ -> I32Binop (I32And , e1', e2'))
      | I32Xor  -> I32Binop (I32Xor , e1', e2')
      | I32Or   -> I32Binop (I32Or  , e1', e2')
      | I32Shl  -> I32Binop (I32Shl , e1', e2')
      | I32ShrS -> I32Binop (I32ShrS, e1', e2')
      | I32ShrU -> I32Binop (I32ShrU, e1', e2')
      | I32RemS -> I32Binop (I32RemS, e1', e2')
      | I32RemU -> I32Binop (I32RemU, e1', e2')
      end
  | I32Unop  (op, e) -> I32Unop (op, rec_simplify e)
  | I32Relop (op, e1, e2) ->
      let e1' = rec_simplify e1
      and e2' = rec_simplify e2 in
      begin match op with
      | I32Eq ->
          begin match e1', e2' with
          | Ptr v1, Ptr v2
          | Ptr v1, Value v2
          | Value v1, Ptr v2
          | Value v1, Value v2 ->
              let ret = Eval_numeric.eval_relop (I32 Ast.I32Op.Eq) v1 v2 in
              Value (Values.value_of_bool ret)
          | _ -> I32Relop (I32Eq, e1', e2')
          end
      | I32Ne ->
          begin match e1', e2' with
          | Ptr v1, Ptr v2
          | Ptr v1, Value v2
          | Value v1, Ptr v2
          | Value v1, Value v2 ->
              let ret = Eval_numeric.eval_relop (I32 Ast.I32Op.Ne) v1 v2 in
              Value (Values.value_of_bool ret)
          | _ -> I32Relop (I32Ne, e1', e2')
          end
      | _ -> I32Relop (op, e1', e2')
      end
  | I32Cvtop (op, e) ->
      let e' = rec_simplify e in
      begin match op, e' with
      | I32ReinterpretFloat, F32Cvtop (Sf32.F32ReinterpretInt, e'') -> e''
      | _ -> I32Cvtop (op, e')
      end
  | I64Cvtop (op, e) ->
      let e' = rec_simplify e in
      begin match op, e' with
      | Si64.I64ReinterpretFloat, F64Cvtop (Sf64.F64ReinterpretInt, e'') -> e''
      | _ -> I64Cvtop (op, e')
      end
  | F32Cvtop (op, e) ->
      let e' = rec_simplify e in
      begin match op, e' with
      | Sf32.F32ReinterpretInt, I32Cvtop (I32ReinterpretFloat, e'') -> e''
      | _ -> F32Cvtop (op, e')
      end
  | F64Cvtop (op, e) ->
      let e' = rec_simplify e in
      begin match op, e' with
      | Sf64.F64ReinterpretInt, I64Cvtop (Si64.I64ReinterpretFloat, e'') -> e''
      | _ -> F64Cvtop (op, e')
      end
  | Extract (e, h, l) ->
      let e' = rec_simplify e in
      begin match e' with
      | Concat (Extract (_, _, _), Concat (_, _)) -> Extract (e', h, l)
      | Concat (e1, e2) ->
          let size_e1 = Types.size (type_of e1)
          and size_e2 = Types.size (type_of e2) in
          (* rec_simplify extraction *)
          if (l = 0) && (h - l) = size_e2 then e2
          else if (l = 4) && (h - l) = size_e1 then e1
          else Extract(e', h, l)
      | _ -> Extract (e', h, l)
      end
  | Concat (e1, e2) ->
      let e1' = rec_simplify e1
      and e2' = rec_simplify e2 in
      begin match e1', e2' with
      | Extract (Value (I64 0L), 4, 1), Extract (I32Binop (I32And, e3, Value (I32 v)), 1, 0) when
        ((v >= 0l) && (v <= 255l)) -> I32Binop (I32And, e3, Value (I32 1l))
      | Extract (Value (I64 v1), h1, l1), Extract (Value (I64 v2), h2, l2) ->
          let v = Int64.(logor (shift_left v1 (h2 * 8)) v2) in
          Extract (Value (I64 v), (h2 - l2) + 1, 0)
      | Extract (e1'', h1, l1), Extract (e2'', h2, l2) ->
          if e1''= e2'' then (
            if (h1 - l2) = (Types.size (type_of e1'')) then e1''
            else Extract (e1'', h1, l2)
          ) else Concat (e1', e2')

      | Extract (e1'', h1, l1), Concat (Extract (e2'', h2, l2), e3) ->
          if e1'' = e2'' then (
            if (h1 - l2) = (Types.size (type_of e1'')) then Concat (e1'', e3)
            else Concat (Extract (e1'', h1, l2), e3)
          ) else (
            match e1'', e2'' with
            (* Because we are here v1 != v2 *)
            | Value (I64 v1), Value (I64 v2) ->
              let v = Int64.(logor (shift_left v1 (h2 * 8)) v2) in
              Concat (Extract (Value (I64 v), h1, l2), e3)
            | _ -> Concat (e1', e2')
          )
(*      | Extract(e1'', 4, 1), Extract(I32Binop(I32And, e3, Value (I32 1l)), )*)
      | _ -> Concat (e1', e2')
      end
  | _ -> e

let simplify ?(extract=false) (e : sym_expr) : sym_expr =
  if !Flags.simplify then new_simplify ~extract:extract e else e

(* not working properly *)
let rewrite (cond : sym_expr) asgn : sym_expr =
  let var, v = asgn in
  let t, x = var in
  let rec loop e =  match e with
    | Ptr p   -> Ptr p
    | Value v -> Value v
    | I32Unop  (op, e')     -> I32Unop  (op, loop e')
    | I32Binop (op, e1, e2) -> I32Binop (op, loop e1, loop e2)
    | I32Relop (op, e1, e2) ->
        (match op with
        | I32Eq | I32Ne -> I32Relop (op, e1, e2)
        | _ -> I32Relop (op, loop e1, loop e2))
    | I32Cvtop (op, e')     -> I32Cvtop (op, loop e')
    | I64Unop  (op, e')     -> I64Unop  (op, loop e')
    | I64Binop (op, e1, e2) -> I64Binop (op, loop e1, loop e2)
    | I64Relop (op, e1, e2) -> I64Relop (op, loop e1, loop e2)
    | I64Cvtop (op, e')     -> I64Cvtop (op, loop e')
    | F32Unop  (op, e')     -> F32Unop  (op, loop e')
    | F32Binop (op, e1, e2) -> F32Binop (op, loop e1, loop e2)
    | F32Relop (op, e1, e2) -> F32Relop (op, loop e1, loop e2)
    | F32Cvtop (op, e')     -> F32Cvtop (op, loop e')
    | F64Unop  (op, e')     -> F64Unop  (op, loop e')
    | F64Binop (op, e1, e2) -> F64Binop (op, loop e1, loop e2)
    | F64Relop (op, e1, e2) -> F64Relop (op, loop e1, loop e2)
    | F64Cvtop (op, e')     -> F64Cvtop (op, loop e')
    | Symbolic (t', x')     ->
        if t' = t && x = x' then Value v
                            else Symbolic (t', x')
    | Extract (e', h, l)    -> Extract (loop e', h, l)
    | Concat (e1, e2)       -> Concat (loop e1, loop e2)
  in loop cond

let mk_relop (e : sym_expr) (t : value_type) : sym_expr =
  let e = simplify e in
  if (is_relop e) then e
  else (
    let zero = Values.default_value t in
    let e' = match t with
      | I32Type -> I32Relop (Si32.I32Ne, e, Value zero)
      | I64Type -> I64Relop (Si64.I64Ne, e, Value zero)
      | F32Type -> F32Relop (Sf32.F32Ne, e, Value zero)
      | F64Type -> F64Relop (Sf64.F64Ne, e, Value zero)
    in simplify e'
  )

let add_constraint
    ?(neg : bool = false)
    (e : sym_expr)
    (pc : path_conditions) : path_conditions =
  let cond =
    let c = to_constraint (simplify e) in
    if neg then Option.map negate_relop c else c
  in Batteries.Option.map_default (fun a -> a :: pc) pc cond
