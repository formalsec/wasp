open Si32
open Types
open Values

type symbolic = SymInt32 | SymInt64 | SymFloat32 | SymFloat64

type boolop   = And | Or

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
  | BoolOp   of boolop   * sym_expr * sym_expr

(*  Pair ( (concrete) Value, (symbolic) Expression)  *)
type sym_value = value * sym_expr

(*  To keep record of the path conditions  *)
type path_conditions = sym_expr list

let type_of_symbolic = function
  | SymInt32   -> I32Type
  | SymInt64   -> I64Type
  | SymFloat32 -> F32Type
  | SymFloat64 -> F64Type

let to_symbolic (t : value_type) (x : string) : sym_expr =
  let symb = begin match t with
    | I32Type -> SymInt32
    | I64Type -> SymInt64
    | F32Type -> SymFloat32
    | F64Type -> SymFloat64
    end
  in Symbolic (symb, x)


let rec type_of (e : sym_expr) : value_type  =
  let rec concat_length (e : sym_expr) : int =
    begin match e with
    | Concat (e1, e2) -> (concat_length e1) + (concat_length e2)
    | Extract (_, h, l) -> h - l
    | e' -> (Types.size (type_of e'))
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
    let len = concat_length e in
    let len = if len < 4 then (Types.size (type_of e1)) + (Types.size (type_of e2))
                         else len 
    in
    begin match len with
    | 4 -> I32Type
    | 8 -> I64Type
    | _ -> failwith "unsupported type length"
    end
  | BoolOp _ -> I32Type
  end

(*  Negates a sym_expr  *)
let rec neg_expr (e : sym_expr) : sym_expr =
  begin match e with 
  (* Value *)
  | Value (I32 0l) -> Value (I32 1l)
  | Value (I32 _)  -> Value (I32 0l)
  (* RelOp *)
  | I32Relop (op, e1, e2) -> I32Relop (Si32.neg_relop op, e1, e2) 
  | I64Relop (op, e1, e2) -> I64Relop (Si64.neg_relop op, e1, e2)
  | F32Relop (op, e1, e2) -> F32Relop (Sf32.neg_relop op, e1, e2)
  | F64Relop (op, e1, e2) -> F64Relop (Sf64.neg_relop op, e1, e2)
  (* BoolOp *)
  | I32Binop (I32And, e1, e2) -> I32Binop(I32Or , neg_expr e1, neg_expr e2)
  | I32Binop (I32Or , e1, e2) -> I32Binop(I32And, neg_expr e1, neg_expr e2)
  | BoolOp (And, e1, e2) -> BoolOp (Or , neg_expr e1, neg_expr e2)
  | BoolOp (Or , e1, e2) -> BoolOp (And, neg_expr e1, neg_expr e2)
  (* Maintain rest *)
  | _ -> e
  end

let and_list (lst : sym_expr list ) : sym_expr =
  assert (not (lst = []));
  let rec loop acc = function
    | []     -> acc
    | h :: t -> loop (BoolOp (And, acc, h)) t
  in loop (List.hd lst) (List.tl lst)

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
  | BoolOp   (op, e1, e2) -> 1 + (length e1) + (length e2)
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
  | BoolOp   (op, e1, e2) -> (get_symbols e1) @ (get_symbols e2)
  end

(*  String representation of an symbolic types  *)
let string_of_symbolic (op : symbolic) : string =
  begin match op with 
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
  | BoolOp (op, e1, e2) ->
      let str_e1 = to_string e1
      and str_e2 = to_string e2
      and str_op =
        match op with
        | And -> "And"
        | Or  -> "Or"
      in
      "(" ^ str_op ^ " " ^ str_e1 ^ " " ^ str_e2 ^ ")"
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
  | BoolOp (op, e1, e2) ->
      let str_e1 = pp_to_string e1
      and str_e2 = pp_to_string e2
      and str_op =
        match op with
        | And -> "/\\"
        | Or  -> "\\/"
      in
      "(" ^ str_e1 ^ " " ^ str_op ^ " " ^ str_e2 ^ ")"
  end

(*  String representation of a list of path conditions  *)
let string_of_pc (pc : path_conditions) : string = 
  List.fold_left (fun acc c -> acc ^ (to_string c) ^ ";  ") "" pc

let pp_string_of_pc (pc : path_conditions) : string = 
  List.fold_left (fun acc e -> acc ^ (pp_to_string e) ^ ";  ") "" pc

let string_of_sym_value (el : sym_value list) : string = 
  List.fold_left (
    fun acc (v, s) -> 
      acc ^ (Values.string_of_value v) ^ ", " ^ (pp_to_string s) ^ "\n"
  ) "" el

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
  | _ -> 
      Printf.printf "ptr expr: %s\n" (to_string e);
      failwith "unsupported pointer arithmetic"
  end
  



let is_relop (e : sym_expr) : bool =
  begin match e with
  | I32Relop _ | I64Relop _ | F32Relop _ | F64Relop _ -> true
  | _ -> false
  end

let rec simplify (e : sym_expr) : sym_expr =
  begin match e with
  | Value v -> Value v
  | I32Binop (op, e1, e2) ->
      let e1' = simplify e1
      and e2' = simplify e2 in
      begin match op with
      | I32Add ->
        begin match e1', e2' with
        | Value v1, Value v2 ->
            let v' = Eval_numeric.eval_binop (I32 Ast.I32Op.Add) v1 v2 in
            Value v'
        | I32Binop (I32Add, e1'', Value (I32 v1)), Value (I32 v2) ->
            I32Binop (I32Add, e1'', Value (I32 (Int32.add v1 v2)))
        | _ -> I32Binop (I32Add, e1', e2')
        end
      | I32Sub  -> I32Binop (I32Sub , e1', e2')
      | I32Mul  -> I32Binop (I32Mul , e1', e2')
      | I32DivS -> I32Binop (I32DivS, e1', e2')
      | I32DivU -> I32Binop (I32DivU, e1', e2')
      | I32And  -> I32Binop (I32And , e1', e2')
      | I32Xor  -> I32Binop (I32Xor , e1', e2')
      | I32Or   -> I32Binop (I32Or  , e1', e2')
      | I32Shl  -> I32Binop (I32Shl , e1', e2')
      | I32ShrS -> I32Binop (I32ShrS, e1', e2')
      | I32ShrU -> I32Binop (I32ShrU, e1', e2')
      | I32RemS -> I32Binop (I32RemS, e1', e2')
      | I32RemU -> I32Binop (I32RemU, e1', e2')
      end
  | I32Unop  (op, e) -> I32Unop (op, simplify e)
  | I32Relop (op, e1, e2) ->
      let e1' = simplify e1
      and e2' = simplify e2 in
      begin match op with
      | I32Eq ->
          begin match e1', e2' with
          | Ptr v1, Ptr v2
          | Value v1, Value v2 ->
              let ret = Eval_numeric.eval_relop (I32 Ast.I32Op.Eq) v1 v2 in
              Value (Values.value_of_bool ret)
          | _ -> I32Relop (I32Eq, e1', e2')
          end
      | I32Ne ->
          begin match e1', e2' with
          | Ptr v1, Ptr v2
          | Value v1, Value v2 ->
              let ret = Eval_numeric.eval_relop (I32 Ast.I32Op.Ne) v1 v2 in
              Value (Values.value_of_bool ret)
          | _ -> I32Relop (I32Ne, e1', e2')
          end
      | _ -> I32Relop (op, e1', e2')
      end
  | Extract (e, h, l) ->
      let mask l h =
        let rec loop x i =
          if i >= h then x
          else loop (Int64.(logor x (shift_left 0xffL (8 * i)))) (i + 1)
        in loop 0L l
      in
      let e' = simplify e in
      begin match e' with
      | Value (I32 v) -> 
          let bit_mask = Int64.to_int32 (mask l h) in
          Value (I32 Int32.(logand (shift_left v (8 * l)) bit_mask))
      | Value (I64 v) ->
          Value (I64 Int64.(logand (shift_left v (8 * l)) (mask l h)))
      | Concat (e1, e2) -> 
          (* Simplify extraction *)
          if (l = 0) && (h - l) = (Types.size (type_of e2)) then e2
          else if (l = 4) && (h - l) = (Types.size (type_of e1)) then e1
          else Extract(e', h, l)
      | _ -> Extract (e', h, l)
      end
  | Concat (e1, e2) ->
      let e1' = simplify e1
      and e2' = simplify e2 in
      begin match e1', e2' with
      | Value (I32 v1), Value (I32 v2) -> Value (I32 (Int32.logor v1 v2))
      | Value (I64 v1), Value (I64 v2) -> Value (I64 (Int64.logor v1 v2))
      | Extract (e1'', h1, l1), Extract (e2'', h2, l2) ->
          if e1''= e2'' then begin
            if (h1 - l2) = (Types.size (type_of e1'')) then e1''
            else Extract (e1'', h1, l2)
          end else Concat (e1', e2')
      | Extract (e1'', h1, l1), Concat (Extract (e2'', h2, l2), e3) ->
          if e1''= e2'' then begin
            if (h1 - l2) = (Types.size (type_of e1'')) then Concat (e1'', e3)
            else Concat (Extract (e1'', h1, l2), e3)
          end else Concat (e1', e2')
      | _ -> Concat (e1', e2')
      end
  | BoolOp (op, e1, e2) ->
      let e1' = simplify e1
      and e2' = simplify e2 in
      BoolOp (op, e1', e2')
  | _ -> e
  end
