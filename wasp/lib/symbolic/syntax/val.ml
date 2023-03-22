open I32
open I64

type symbolic =
  | SymInt8
  | SymInt16
  | SymInt32
  | SymInt64
  | SymFloat32
  | SymFloat64

type sym_expr =
  (* Value *)
  | Value of Interpreter.Values.value
  (* Ptr *)
  | SymPtr of int32 * sym_expr
  (* I32 operations *)
  | I32Binop of I32.binop * sym_expr * sym_expr
  | I32Unop of I32.unop * sym_expr
  | I32Relop of I32.relop * sym_expr * sym_expr
  | I32Cvtop of I32.cvtop * sym_expr
  (* I64 operations *)
  | I64Binop of I64.binop * sym_expr * sym_expr
  | I64Unop of I64.unop * sym_expr
  | I64Relop of I64.relop * sym_expr * sym_expr
  | I64Cvtop of I64.cvtop * sym_expr
  (* F32 operations *)
  | F32Binop of F32.binop * sym_expr * sym_expr
  | F32Unop of F32.unop * sym_expr
  | F32Relop of F32.relop * sym_expr * sym_expr
  | F32Cvtop of F32.cvtop * sym_expr
  (* F64 operations *)
  | F64Binop of F64.binop * sym_expr * sym_expr
  | F64Unop of F64.unop * sym_expr
  | F64Relop of F64.relop * sym_expr * sym_expr
  | F64Cvtop of F64.cvtop * sym_expr
  (* Symbolic *)
  | Symbolic of symbolic * string
  (* Encoding Auxiliary *)
  | Extract of sym_expr * int * int
  | Concat of sym_expr * sym_expr

(*  Pair ( (concrete) Value, (symbolic) Expression)  *)
type sym_value = Interpreter.Values.value * sym_expr

(*  To keep record of the path conditions  *)
type path_conditions = sym_expr list

let type_of_symbolic = function
  | SymInt8 -> Interpreter.Types.I32Type
  | SymInt16 -> Interpreter.Types.I32Type
  | SymInt32 -> Interpreter.Types.I32Type
  | SymInt64 -> Interpreter.Types.I64Type
  | SymFloat32 -> Interpreter.Types.F32Type
  | SymFloat64 -> Interpreter.Types.F64Type

let to_symbolic (t : Interpreter.Types.value_type) (x : string) : sym_expr =
  let symb =
    match t with
    | Interpreter.Types.I32Type -> SymInt32
    | Interpreter.Types.I64Type -> SymInt64
    | Interpreter.Types.F32Type -> SymFloat32
    | Interpreter.Types.F64Type -> SymFloat64
  in
  Symbolic (symb, x)

let negate_relop (e : sym_expr) : sym_expr =
  match e with
  (* Relop *)
  | I32Relop (op, e1, e2) -> I32Relop (I32.neg_relop op, e1, e2)
  | I64Relop (op, e1, e2) -> I64Relop (I64.neg_relop op, e1, e2)
  | F32Relop (op, e1, e2) -> F32Relop (F32.neg_relop op, e1, e2)
  | F64Relop (op, e1, e2) -> F64Relop (F64.neg_relop op, e1, e2)
  | _ -> failwith "Not a relop"

(* Measure complexity of formulas *)
let rec length (e : sym_expr) : int =
  match e with
  | Value v -> 1
  | SymPtr _ -> 1
  (* I32 *)
  | I32Unop (op, e) -> 1 + length e
  | I32Binop (op, e1, e2) -> 1 + length e1 + length e2
  | I32Relop (op, e1, e2) -> 1 + length e1 + length e2
  | I32Cvtop (op, e) -> 1 + length e
  (* I64 *)
  | I64Unop (op, e) -> 1 + length e
  | I64Binop (op, e1, e2) -> 1 + length e1 + length e2
  | I64Relop (op, e1, e2) -> 1 + length e1 + length e2
  | I64Cvtop (op, e) -> 1 + length e
  (* F32 *)
  | F32Unop (op, e) -> 1 + length e
  | F32Binop (op, e1, e2) -> 1 + length e1 + length e2
  | F32Relop (op, e1, e2) -> 1 + length e1 + length e2
  | F32Cvtop (op, e) -> 1 + length e
  (* F64 *)
  | F64Unop (op, e) -> 1 + length e
  | F64Binop (op, e1, e2) -> 1 + length e1 + length e2
  | F64Relop (op, e1, e2) -> 1 + length e1 + length e2
  | F64Cvtop (op, e) -> 1 + length e
  (* Symbol *)
  | Symbolic (s, x) -> 1
  | Extract (e, _, _) -> 1 + length e
  | Concat (e1, e2) -> 1 + length e1 + length e2

(*  Retrieves the symbolic variables  *)
let rec get_symbols (e : sym_expr) : (string * symbolic) list =
  match e with
  (* Value - holds no symbols *)
  | Value _ -> []
  | SymPtr (_, offset) -> get_symbols offset
  (* I32 *)
  | I32Unop (op, e1) -> get_symbols e1
  | I32Binop (op, e1, e2) -> get_symbols e1 @ get_symbols e2
  | I32Relop (op, e1, e2) -> get_symbols e1 @ get_symbols e2
  | I32Cvtop (op, e) -> get_symbols e
  (* I64 *)
  | I64Unop (op, e1) -> get_symbols e1
  | I64Binop (op, e1, e2) -> get_symbols e1 @ get_symbols e2
  | I64Relop (op, e1, e2) -> get_symbols e1 @ get_symbols e2
  | I64Cvtop (op, e) -> get_symbols e
  (* F32 *)
  | F32Unop (op, e1) -> get_symbols e1
  | F32Binop (op, e1, e2) -> get_symbols e1 @ get_symbols e2
  | F32Relop (op, e1, e2) -> get_symbols e1 @ get_symbols e2
  | F32Cvtop (op, e) -> get_symbols e
  (* F64 *)
  | F64Unop (op, e1) -> get_symbols e1
  | F64Binop (op, e1, e2) -> get_symbols e1 @ get_symbols e2
  | F64Relop (op, e1, e2) -> get_symbols e1 @ get_symbols e2
  | F64Cvtop (op, e) -> get_symbols e
  (* Symbol *)
  | Symbolic (t, x) -> [ (x, t) ]
  | Extract (e, _, _) -> get_symbols e
  | Concat (e1, e2) -> get_symbols e1 @ get_symbols e2

(*  String representation of an symbolic types  *)
let string_of_symbolic (op : symbolic) : string =
  match op with
  | SymInt8 -> "SymInt8"
  | SymInt16 -> "SymInt16"
  | SymInt32 -> "SymInt32"
  | SymInt64 -> "SymInt64"
  | SymFloat32 -> "SymFloat32"
  | SymFloat64 -> "SymFloat64"

(*  String representation of a sym_expr  *)
let rec to_string (e : sym_expr) : string =
  match e with
  | Value v -> Interpreter.Values.string_of_value v
  | SymPtr (base, offset) ->
      let str_o = to_string offset in
      "(SymPtr " ^ Int32.to_string base ^ " + " ^ str_o ^ ")"
  (* I32 *)
  | I32Unop (op, e) ->
      let str_e = to_string e and str_op = I32.string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | I32Binop (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = I32.string_of_binop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | I32Relop (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = I32.string_of_relop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | I32Cvtop (op, e) ->
      let str_e = to_string e and str_op = I32.string_of_cvtop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  (* I64 *)
  | I64Unop (op, e) ->
      let str_e = to_string e and str_op = I64.string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | I64Binop (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = I64.string_of_binop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | I64Relop (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = I64.string_of_relop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | I64Cvtop (op, e) ->
      let str_e = to_string e and str_op = I64.string_of_cvtop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  (* F32 *)
  | F32Unop (op, e) ->
      let str_e = to_string e and str_op = F32.string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | F32Binop (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = F32.string_of_binop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | F32Relop (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = F32.string_of_relop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | F32Cvtop (op, e) ->
      let str_e = to_string e and str_op = F32.string_of_cvtop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  (* F64 *)
  | F64Unop (op, e) ->
      let str_e = to_string e and str_op = F64.string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | F64Binop (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = F64.string_of_binop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | F64Relop (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op = F64.string_of_relop op in
      "(" ^ str_op ^ " " ^ str_e1 ^ ", " ^ str_e2 ^ ")"
  | F64Cvtop (op, e) ->
      let str_e = to_string e and str_op = F64.string_of_cvtop op in
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
      let str_e1 = to_string e1 and str_e2 = to_string e2 in
      "(Concat " ^ str_e1 ^ " " ^ str_e2 ^ ")"

let rec pp_to_string (e : sym_expr) : string =
  match e with
  | Value v -> Interpreter.Values.string_of_value v
  | SymPtr (base, offset) ->
      let str_o = pp_to_string offset in
      "(SymPtr " ^ Int32.to_string base ^ " + " ^ str_o ^ ")"
  (* I32 *)
  | I32Unop (op, e) ->
      let str_e = pp_to_string e and str_op = I32.pp_string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | I32Binop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = I32.pp_string_of_binop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | I32Relop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = I32.pp_string_of_relop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | I32Cvtop (op, e) ->
      let str_e = pp_to_string e and str_op = I32.pp_string_of_cvtop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  (* I64 *)
  | I64Unop (op, e) ->
      let str_e = pp_to_string e and str_op = I64.pp_string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | I64Binop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = I64.pp_string_of_binop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | I64Relop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = I64.pp_string_of_relop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | I64Cvtop (op, e) ->
      let str_e = pp_to_string e and str_op = I64.pp_string_of_cvtop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  (* F32 *)
  | F32Unop (op, e) ->
      let str_e = pp_to_string e and str_op = F32.pp_string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | F32Binop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = F32.pp_string_of_binop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | F32Relop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = F32.pp_string_of_relop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | F32Cvtop (op, e) ->
      let str_e = pp_to_string e and str_op = F32.pp_string_of_cvtop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  (* F64 *)
  | F64Unop (op, e) ->
      let str_e = pp_to_string e and str_op = F64.pp_string_of_unop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | F64Binop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = F64.pp_string_of_binop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | F64Relop (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op = F64.pp_string_of_relop op in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  | F64Cvtop (op, e) ->
      let str_e = pp_to_string e and str_op = F64.pp_string_of_cvtop op in
      "(" ^ str_op ^ " " ^ str_e ^ ")"
  | Symbolic (s, x) -> "#" ^ x
  | Extract (e, h, l) ->
      let str_l = string_of_int l
      and str_h = string_of_int h
      and str_e = pp_to_string e in
      str_e ^ "[" ^ str_l ^ ":" ^ str_h ^ "]"
  | Concat (e1, e2) ->
      let str_e1 = pp_to_string e1 and str_e2 = pp_to_string e2 in
      "(" ^ str_e1 ^ " ++ " ^ str_e2 ^ ")"

(*  String representation of a list of path conditions  *)
let string_of_pc (pc : path_conditions) : string =
  List.fold_left (fun acc c -> acc ^ pp_to_string c ^ ";\n  ") "" pc

let pp_string_of_pc (pc : path_conditions) : string =
  List.fold_left (fun acc e -> acc ^ pp_to_string e ^ ";  ") "" pc

let string_of_sym_value (el : sym_value list) : string =
  List.fold_left
    (fun acc (v, s) ->
      acc ^ Interpreter.Values.string_of_value v ^ ", " ^ pp_to_string s ^ "\n")
    "" el

let rec type_of (e : sym_expr) : Interpreter.Types.value_type =
  let rec concat_length (e' : sym_expr) : int =
    match e' with
    | Value v -> Interpreter.Types.size (Interpreter.Values.type_of v)
    | SymPtr _ -> 4
    | I32Unop _ -> 4
    | I32Binop _ -> 4
    | I32Relop _ -> 4
    | I32Cvtop _ -> 4
    | I64Unop _ -> 8
    | I64Binop _ -> 8
    | I64Relop _ -> 8
    | I64Cvtop _ -> 8
    | F32Unop _ -> 4
    | F32Binop _ -> 4
    | F32Relop _ -> 4
    | F32Cvtop _ -> 4
    | F64Unop _ -> 8
    | F64Binop _ -> 8
    | F64Relop _ -> 8
    | F64Cvtop _ -> 8
    | Symbolic (e'', _) -> (
        match e'' with
        | SymInt8 -> 1
        | SymInt16 -> 2
        | SymInt32 -> 4
        | SymInt64 -> 8
        | SymFloat32 -> 4
        | SymFloat64 -> 8)
    | Concat (e1, e2) -> concat_length e1 + concat_length e2
    | Extract (_, h, l) -> h - l
  in
  match e with
  | Value v -> Interpreter.Values.type_of v
  | SymPtr _ -> Interpreter.Types.I32Type
  | I32Unop _ -> Interpreter.Types.I32Type
  | I32Binop _ -> Interpreter.Types.I32Type
  | I32Relop _ -> Interpreter.Types.I32Type
  | I32Cvtop _ -> Interpreter.Types.I32Type
  | I64Unop _ -> Interpreter.Types.I64Type
  | I64Binop _ -> Interpreter.Types.I64Type
  | I64Relop _ -> Interpreter.Types.I32Type
  | I64Cvtop _ -> Interpreter.Types.I64Type
  | F32Unop _ -> Interpreter.Types.F32Type
  | F32Binop _ -> Interpreter.Types.F32Type
  | F32Relop _ -> Interpreter.Types.I32Type
  | F32Cvtop _ -> Interpreter.Types.F32Type
  | F64Unop _ -> Interpreter.Types.F64Type
  | F64Binop _ -> Interpreter.Types.F64Type
  | F64Relop _ -> Interpreter.Types.I32Type
  | F64Cvtop _ -> Interpreter.Types.F64Type
  | Symbolic (e, _) -> type_of_symbolic e
  | Extract (e, h, l) -> (
      match h - l with
      | 4 -> Interpreter.Types.I32Type
      | 8 -> Interpreter.Types.I64Type
      | _ -> failwith "unsupported type length")
  | Concat (e1, e2) -> (
      let len = concat_length (Concat (e1, e2)) in
      let len =
        if len < 4 then
          Interpreter.Types.size (type_of e1)
          + Interpreter.Types.size (type_of e2)
        else len
      in
      match len with
      | 4 -> Interpreter.Types.I32Type
      | 8 -> Interpreter.Types.I64Type
      | _ -> failwith "unsupported type length")

let rec get_ptr (e : sym_expr) : Interpreter.Values.value option =
  (* FIXME: this function can be "simplified" *)
  match e with
  | Value _ -> None
  | SymPtr (base, _) -> Some (Interpreter.Values.I32 base)
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

let concretize_ptr (e : sym_expr) : Interpreter.Values.value option =
  (* TODO: this should work with symbolic pointers *)
  (* would probably introduce Memory Objects here *)
  let open Interpreter.Values in
  match e with
  | Value p -> Some p
  | SymPtr (base, Value (I32 offset)) -> Some (I32 (Int32.add base offset))
  | _ -> None

let concretize_base_ptr (e : sym_expr) : int32 option =
  match e with SymPtr (base, _) -> Some base | _ -> None

let is_value (e : sym_expr) : bool = match e with Value _ -> true | _ -> false

let is_concrete (e : sym_expr) : bool =
  match e with Value _ | SymPtr (_, Value _) -> true | _ -> false

let is_relop (e : sym_expr) : bool =
  match e with
  | I32Relop _ | I64Relop _ | F32Relop _ | F64Relop _ -> true
  | _ -> false

let to_constraint (e : sym_expr) : sym_expr option =
  if is_concrete e then None
  else if is_relop e then Some e
  else Some (I32Relop (I32Ne, e, Value (Interpreter.Values.I32 0l)))

let i64binop_to_astop (op : I64.binop) =
  let open Interpreter in
  match op with
  | I64Add -> Ast.I64Op.Add
  | I64And -> Ast.I64Op.And
  | I64Or -> Ast.I64Op.Or
  | I64Sub -> Ast.I64Op.Sub
  | I64DivS -> Ast.I64Op.DivS
  | I64DivU -> Ast.I64Op.DivU
  | I64Xor -> Ast.I64Op.Xor
  | I64Mul -> Ast.I64Op.Mul
  | I64Shl -> Ast.I64Op.Shl
  | I64ShrS -> Ast.I64Op.ShrS
  | I64ShrU -> Ast.I64Op.ShrU
  | I64RemS -> Ast.I64Op.RemS
  | I64RemU -> Ast.I64Op.RemU

let i32binop_to_astop (op : I32.binop) =
  let open Interpreter in
  match op with
  | I32Add -> Ast.I32Op.Add
  | I32And -> Ast.I32Op.And
  | I32Or -> Ast.I32Op.Or
  | I32Sub -> Ast.I32Op.Sub
  | I32DivS -> Ast.I32Op.DivS
  | I32DivU -> Ast.I32Op.DivU
  | I32Xor -> Ast.I32Op.Xor
  | I32Mul -> Ast.I32Op.Mul
  | I32Shl -> Ast.I32Op.Shl
  | I32ShrS -> Ast.I32Op.ShrS
  | I32ShrU -> Ast.I32Op.ShrU
  | I32RemS -> Ast.I32Op.RemS
  | I32RemU -> Ast.I32Op.RemU

let i32relop_to_astop (op : I32.relop) =
  let open Interpreter in
  match op with
  | I32Eq -> Ast.I32Op.Eq
  | I32Ne -> Ast.I32Op.Ne
  | I32LtU -> Ast.I32Op.LtU
  | I32GtU -> Ast.I32Op.GtU
  | I32LtS -> Ast.I32Op.LtS
  | I32GtS -> Ast.I32Op.GtS
  | I32LeU -> Ast.I32Op.LeU
  | I32GeU -> Ast.I32Op.GeU
  | I32LeS -> Ast.I32Op.LeS
  | I32GeS -> Ast.I32Op.GeS

let nland64 (x : int64) n =
  let rec loop x' n' acc =
    if n' = 0 then Int64.logand x' acc
    else loop x' (n' - 1) Int64.(logor (shift_left acc 8) 0xffL)
  in
  loop x n 0L

let nland32 (x : int32) n =
  let rec loop x' n' acc =
    if n' = 0 then Int32.logand x' acc
    else loop x' (n' - 1) Int32.(logor (shift_left acc 8) 0xffl)
  in
  loop x n 0l

let rec new_simplify ?(extract = true) (e : sym_expr) : sym_expr =
  let open Interpreter in
  match e with
  | Value v -> Value v
  | SymPtr (base, offset) -> SymPtr (base, new_simplify offset)
  | I32Binop (op, e1, e2) -> (
      let e1' = new_simplify e1 and e2' = new_simplify e2 in
      match (e1', e2') with
      | SymPtr (b1, os1), SymPtr (b2, os2) -> (
          match op with
          | I32Sub when b1 = b2 -> new_simplify (I32Binop (I32Sub, os1, os2))
          | _ -> I32Binop (op, e1', e2'))
      | SymPtr (base, offset), _ -> (
          match op with
          | I32Add ->
              let new_offset = new_simplify (I32Binop (I32Add, offset, e2')) in
              new_simplify (SymPtr (base, new_offset))
          | I32Sub ->
              let new_offset = new_simplify (I32Binop (I32Sub, offset, e2')) in
              new_simplify (SymPtr (base, new_offset))
          | _ -> I32Binop (op, e1', e2'))
      | _, SymPtr (base, offset) -> (
          match op with
          | I32Add ->
              let new_offset = new_simplify (I32Binop (I32Add, offset, e1')) in
              new_simplify (SymPtr (base, new_offset))
          | _ -> I32Binop (op, e1', e2'))
      | Value (Values.I32 0l), _ -> (
          match op with
          | I32Add | I32Or | I32Sub -> e2'
          | I32And | I32DivS | I32DivU | I32Mul | I32RemS | I32RemU ->
              Value (Values.I32 0l)
          | _ -> I32Binop (op, e1', e2'))
      | _, Value (Values.I32 0l) -> (
          match op with
          | I32Add | I32Or | I32Sub -> e1'
          | I32And | I32Mul -> Value (Values.I32 0l)
          | _ -> I32Binop (op, e1', e2'))
      | Value v1, Value v2 ->
          Value
            (Eval_numeric.eval_binop (Values.I32 (i32binop_to_astop op)) v1 v2)
      | I32Binop (op2, x, Value v1), Value v2 when not (is_value x) -> (
          match (op, op2) with
          | I32Add, I32Add ->
              let v =
                Eval_numeric.eval_binop (Values.I32 Ast.I32Op.Add) v1 v2
              in
              I32Binop (I32Add, x, Value v)
          | I32Add, I32Sub | I32Sub, I32Add ->
              let v =
                Eval_numeric.eval_binop (Values.I32 Ast.I32Op.Sub) v1 v2
              in
              I32Binop (I32Add, x, Value v)
          | I32Sub, I32Sub ->
              let v =
                Eval_numeric.eval_binop (Values.I32 Ast.I32Op.Add) v1 v2
              in
              I32Binop (I32Sub, x, Value v)
          | _, _ -> I32Binop (op, e1', e2'))
      | (bop, Value (Values.I32 1l) | Value (Values.I32 1l), bop)
        when is_relop bop && op = I32And ->
          bop
      | _ -> I32Binop (op, e1', e2'))
  | I64Binop (op, e1, e2) -> (
      let e1' = new_simplify e1 and e2' = new_simplify e2 in
      match (e1', e2') with
      | SymPtr (b1, os1), SymPtr (b2, os2) -> (
          match op with
          | I64Sub when b1 = b2 -> new_simplify (I64Binop (I64Sub, os1, os2))
          | _ -> I64Binop (op, e1', e2'))
      | SymPtr (base, offset), _ -> (
          match op with
          | I64Add ->
              let new_offset = new_simplify (I64Binop (I64Add, offset, e2')) in
              new_simplify (SymPtr (base, new_offset))
          | I64Sub ->
              let new_offset = new_simplify (I64Binop (I64Sub, offset, e2')) in
              new_simplify (SymPtr (base, new_offset))
          | _ -> I64Binop (op, e1', e2'))
      | _, SymPtr (base, offset) -> (
          match op with
          | I64Add ->
              let new_offset = new_simplify (I64Binop (I64Add, offset, e1')) in
              new_simplify (SymPtr (base, new_offset))
          | _ -> I64Binop (op, e1', e2'))
      | Value (Values.I64 0L), _ -> (
          match op with
          | I64Add | I64Or | I64Sub -> e2'
          | I64And | I64DivS | I64DivU | I64Mul | I64RemS | I64RemU ->
              Value (Values.I64 0L)
          | _ -> I64Binop (op, e1', e2'))
      | _, Value (Values.I64 0L) -> (
          match op with
          | I64Add | I64Or | I64Sub -> e1'
          | I64And | I64Mul -> Value (Values.I64 0L)
          | _ -> I64Binop (op, e1', e2'))
      | Value v1, Value v2 ->
          Value
            (Eval_numeric.eval_binop (Values.I64 (i64binop_to_astop op)) v1 v2)
      | I64Binop (op2, x, Value v1), Value v2 when not (is_value x) -> (
          match (op, op2) with
          | I64Add, I64Add ->
              let v =
                Eval_numeric.eval_binop (Values.I64 Ast.I64Op.Add) v1 v2
              in
              I64Binop (I64Add, x, Value v)
          | I64Add, I64Sub | I64Sub, I64Add ->
              let v =
                Eval_numeric.eval_binop (Values.I64 Ast.I64Op.Sub) v1 v2
              in
              I64Binop (I64Add, x, Value v)
          | I64Sub, I64Sub ->
              let v =
                Eval_numeric.eval_binop (Values.I64 Ast.I64Op.Add) v1 v2
              in
              I64Binop (I64Sub, x, Value v)
          | _, _ -> I64Binop (op, e1', e2'))
      | (bop, Value (Values.I64 1L) | Value (Values.I64 1L), bop)
        when is_relop bop && op = I64And ->
          bop
      | _ -> I64Binop (op, e1', e2'))
  | I32Relop (op, e1, e2) -> (
      let open Values in
      let e1' = new_simplify e1 and e2' = new_simplify e2 in
      match (e1', e2') with
      | Value v1, Value v2 ->
          let op' = I32 (i32relop_to_astop op) in
          let ret = Eval_numeric.eval_relop op' v1 v2 in
          Value (Interpreter.Values.value_of_bool ret)
      | SymPtr (_, _), Value (I32 0l) | Value (I32 0l), SymPtr (_, _) -> (
          match op with
          | I32Eq -> Value (I32 0l)
          | I32Ne -> Value (I32 1l)
          | _ -> I32Relop (op, e1', e2'))
      | SymPtr (b1, os1), SymPtr (b2, os2) -> (
          match op with
          | I32Eq when b1 = b2 -> I32Relop (I32Eq, os1, os2)
          | I32Eq when b1 != b2 -> Value (I32 0l)
          | I32Ne when b1 = b2 -> I32Relop (I32Ne, os1, os2)
          | I32Ne when b1 != b2 -> Value (I32 1l)
          | I32LtU when b1 = b2 -> I32Relop (I32LtU, os1, os2)
          | I32LeU when b1 = b2 -> I32Relop (I32LeU, os1, os2)
          | I32LtU -> I32Relop (I32LtU, Value (I32 b1), Value (I32 b2))
          | I32LeU -> I32Relop (I32LeU, Value (I32 b1), Value (I32 b2))
          | I32GtU when b1 = b2 -> I32Relop (I32GtU, os1, os2)
          | I32GeU when b1 = b2 -> I32Relop (I32GeU, os1, os2)
          | I32GtU -> I32Relop (I32GtU, Value (I32 b1), Value (I32 b2))
          | I32GeU -> I32Relop (I32GeU, Value (I32 b1), Value (I32 b2))
          | _ -> I32Relop (op, e1', e2'))
      | _ -> I32Relop (op, e1', e2'))
  | Extract (s, h, l) when extract = false -> e
  | Extract (s, h, l) when extract = true -> (
      match s with
      | Value (Values.I64 x) ->
          let x' = nland64 (Int64.shift_right x (l * 8)) (h - l) in
          Value (Values.I64 x')
      | _ when h - l = Interpreter.Types.size (type_of s) -> s
      | _ -> e)
  | Concat (e1, e2) -> (
      let open Values in
      let e1' = new_simplify ~extract:false e1
      and e2' = new_simplify ~extract:false e2 in
      match (e1', e2') with
      | Extract (Value (I64 x2), h2, l2), Extract (Value (I64 x1), h1, l1) ->
          let d1 = h1 - l1 and d2 = h2 - l2 in
          let x1' = nland64 (Int64.shift_right x1 (l1 * 8)) d1
          and x2' = nland64 (Int64.shift_right x2 (l2 * 8)) d2 in
          let x = Int64.(logor (shift_left x2' (d1 * 8)) x1') in
          Extract (Value (I64 x), d1 + d2, 0)
      | Extract (Value (I32 x2), h2, l2), Extract (Value (I32 x1), h1, l1) ->
          let d1 = h1 - l1 and d2 = h2 - l2 in
          let x1' = nland32 (Int32.shift_right x1 (l1 * 8)) d1
          and x2' = nland32 (Int32.shift_right x2 (l2 * 8)) d2 in
          let x = Int32.(logor (shift_left x2' (d1 * 8)) x1') in
          Extract (Value (I32 x), d1 + d2, 0)
      | Extract (s1, h, m1), Extract (s2, m2, l) when s1 = s2 && m1 = m2 ->
          Extract (s1, h, l)
      | ( Extract (Value (I64 x2), h2, l2),
          Concat (Extract (Value (I64 x1), h1, l1), se) )
        when not (is_value se) ->
          let d1 = h1 - l1 and d2 = h2 - l2 in
          let x1' = nland64 (Int64.shift_right x1 (l1 * 8)) d1
          and x2' = nland64 (Int64.shift_right x2 (l2 * 8)) d2 in
          let x = Int64.(logor (shift_left x2' (d1 * 8)) x1') in
          Concat (Extract (Value (I64 x), d1 + d2, 0), se)
      | _ -> Concat (e1', e2'))
  | _ -> e

let simplify ?(extract = false) (e : sym_expr) : sym_expr =
  if !Interpreter.Flags.simplify then new_simplify ~extract e else e

(* not working properly *)
let rewrite (cond : sym_expr) asgn : sym_expr =
  let var, v = asgn in
  let t, x = var in
  let rec loop (e : sym_expr) : sym_expr =
    match e with
    | Value v -> Value v
    | SymPtr (base, offset) -> SymPtr (base, offset)
    | I32Unop (op, e') -> I32Unop (op, loop e')
    | I32Binop (op, e1, e2) -> I32Binop (op, loop e1, loop e2)
    | I32Relop (op, e1, e2) -> (
        match op with
        | I32Eq | I32Ne -> I32Relop (op, e1, e2)
        | _ -> I32Relop (op, loop e1, loop e2))
    | I32Cvtop (op, e') -> I32Cvtop (op, loop e')
    | I64Unop (op, e') -> I64Unop (op, loop e')
    | I64Binop (op, e1, e2) -> I64Binop (op, loop e1, loop e2)
    | I64Relop (op, e1, e2) -> I64Relop (op, loop e1, loop e2)
    | I64Cvtop (op, e') -> I64Cvtop (op, loop e')
    | F32Unop (op, e') -> F32Unop (op, loop e')
    | F32Binop (op, e1, e2) -> F32Binop (op, loop e1, loop e2)
    | F32Relop (op, e1, e2) -> F32Relop (op, loop e1, loop e2)
    | F32Cvtop (op, e') -> F32Cvtop (op, loop e')
    | F64Unop (op, e') -> F64Unop (op, loop e')
    | F64Binop (op, e1, e2) -> F64Binop (op, loop e1, loop e2)
    | F64Relop (op, e1, e2) -> F64Relop (op, loop e1, loop e2)
    | F64Cvtop (op, e') -> F64Cvtop (op, loop e')
    | Symbolic (t', x') ->
        if t' = t && x = x' then Value v else Symbolic (t', x')
    | Extract (e', h, l) -> Extract (loop e', h, l)
    | Concat (e1, e2) -> Concat (loop e1, loop e2)
  in
  loop cond

let mk_relop (e : sym_expr) (t : Interpreter.Types.value_type) : sym_expr =
  let e = simplify e in
  if is_relop e then e
  else
    let zero = Interpreter.Values.default_value t in
    let e' =
      match t with
      | Interpreter.Types.I32Type -> I32Relop (I32.I32Ne, e, Value zero)
      | Interpreter.Types.I64Type -> I64Relop (I64.I64Ne, e, Value zero)
      | Interpreter.Types.F32Type -> F32Relop (F32.F32Ne, e, Value zero)
      | Interpreter.Types.F64Type -> F64Relop (F64.F64Ne, e, Value zero)
    in
    simplify e'

let add_constraint ?(neg : bool = false) (e : sym_expr) (pc : path_conditions) :
    path_conditions =
  let cond =
    let c = to_constraint (simplify e) in
    if neg then Option.map negate_relop c else c
  in
  Batteries.Option.map_default (fun a -> a :: pc) pc cond
