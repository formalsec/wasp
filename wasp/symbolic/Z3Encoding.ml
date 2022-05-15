open Z3

(*  Encoding option  *)
type encoding =
  | WithReals
  | WithFPA

(*  String representation of the encoding used  *)
let string_of_enc enc =
  match enc with
  | WithReals -> "REAL"
  | WithFPA -> "FPA"

(*  The encoding to use  *)
let encoding = ref WithReals

(*  Match an operation according to the encoding option used  *)
let match_enc msg x y =
  match (!encoding) with
  | WithReals -> x
  | WithFPA   -> y

(*  TYPE CONSTRUCTORS  *)
type type_constructors = {
  boolean_type_constructor : FuncDecl.func_decl;
  number_type_constructor  : FuncDecl.func_decl;
  int_type_constructor     : FuncDecl.func_decl;
  string_type_constructor  : FuncDecl.func_decl;
}

(*  AXIOMATIZED OPERATIONS --> for string length  *)
type axiomatized_operations = {
  slen_fun    : FuncDecl.func_decl;
  bool_to_int : FuncDecl.func_decl;
}

(*  Z3 CONSTRUCTORS, ACCESSORS AND RECOGNIZERS  *)
type z3_values = {
  (*  Constructors  *)
  bool_constructor   : FuncDecl.func_decl;
  num_constructor    : FuncDecl.func_decl;
  string_constructor : FuncDecl.func_decl;
  int_constructor    : FuncDecl.func_decl;

  (*  Accessors  *)
  bool_accessor      : FuncDecl.func_decl;
  num_accessor       : FuncDecl.func_decl;
  string_accessor    : FuncDecl.func_decl;
  int_accessor       : FuncDecl.func_decl;

  (*  Recognizers  *)
  bool_recognizer    : FuncDecl.func_decl;
  num_recognizer     : FuncDecl.func_decl;
  string_recognizer  : FuncDecl.func_decl;
  int_recognizer     : FuncDecl.func_decl;
}

(*  Configurations  *)
let cfg = [("model", "true"); ("proof", "true"); ("unsat_core", "true"); ("timeout", "16384")]
let ctx : context = (mk_context cfg)

(*  Sorting  *)
let booleans_sort = Boolean.mk_sort ctx
let ints_sort     = Arithmetic.Integer.mk_sort ctx
let reals_sort    = Arithmetic.Real.mk_sort ctx
let fp_sort       = FloatingPoint.mk_sort_64 ctx
let numbers_sort  = match_enc "mk_sort" reals_sort fp_sort

let rm = FloatingPoint.mk_const ctx (Symbol.mk_string ctx "rm") (FloatingPoint.RoundingMode.mk_sort ctx)
let mk_string_symb s = Symbol.mk_string ctx s

(*  ---- OPERATIONS ----  *)

(*  Real/FPA operations  *)
let mk_const = match_enc "mk_const" (Arithmetic.Real.mk_const ctx) (fun (s : Symbol.symbol) -> FloatingPoint.mk_const ctx s fp_sort)
let mk_num_i = match_enc "mk_num_i" (Arithmetic.Real.mk_numeral_i ctx) (fun i -> FloatingPoint.mk_numeral_i ctx i fp_sort)
let mk_num_s = match_enc "mk_num_s" (Arithmetic.Real.mk_numeral_s ctx) (fun s -> FloatingPoint.mk_numeral_s ctx s fp_sort)

let mk_lt    = match_enc "mk_lt" Arithmetic.mk_lt FloatingPoint.mk_lt
let mk_le    = match_enc "mk_le" Arithmetic.mk_le FloatingPoint.mk_leq
let mk_ge    = match_enc "mk_ge" Arithmetic.mk_ge FloatingPoint.mk_geq
let mk_gt    = match_enc "mk_gt" Arithmetic.mk_gt FloatingPoint.mk_gt
let mk_add   = match_enc "mk_add" (fun e1 e2 -> Arithmetic.mk_add ctx [e1; e2]) (fun e1 e2 -> FloatingPoint.mk_add ctx rm e1 e2)
let mk_sub   = match_enc "mk_sub" (fun e1 e2 -> Arithmetic.mk_sub ctx [e1; e2]) (fun e1 e2 -> FloatingPoint.mk_sub ctx rm e1 e2)
let mk_mul   = match_enc "mk_mul" (fun e1 e2 -> Arithmetic.mk_mul ctx [e1; e2]) (fun e1 e2 -> FloatingPoint.mk_mul ctx rm e1 e2)
let mk_div   = match_enc "mk_div" (fun e1 e2 -> Arithmetic.mk_div ctx  e1  e2 ) (fun e1 e2 -> FloatingPoint.mk_div ctx rm e1 e2)

(*  Integer operations  *)
let mk_int_i = Arithmetic.Integer.mk_numeral_i ctx
let mk_int_s = Arithmetic.Integer.mk_numeral_s ctx

let mk_add_i = (fun e1 e2 -> Arithmetic.mk_add ctx [e1; e2])
let mk_sub_i = (fun e1 e2 -> Arithmetic.mk_sub ctx [e1; e2]) 
let mk_mul_i = (fun e1 e2 -> Arithmetic.mk_mul ctx [e1; e2])
let mk_div_i = (fun e1 e2 -> Arithmetic.mk_div ctx  e1  e2 )
let mk_lt_i = Arithmetic.mk_lt 
let mk_le_i = Arithmetic.mk_le 
let mk_ge_i = Arithmetic.mk_ge
let mk_gt_i = Arithmetic.mk_gt

(*  ------------------  *)

let z3_wasm_literal_sort, wasm_lit_operations =
  (*  wasm type constructors  *)
  let wasm_bool_constructor =
    Datatype.mk_constructor ctx (mk_string_symb "Bool") (mk_string_symb "isBool")
      [(mk_string_symb "bValue")] [Some booleans_sort] [0] in
  let wasm_num_constructor =
    Datatype.mk_constructor ctx (mk_string_symb "Num") (mk_string_symb "isNum")
      [(mk_string_symb "nValue")] [Some numbers_sort] [0] in
  let wasm_string_constructor =
    Datatype.mk_constructor ctx (mk_string_symb "String") (mk_string_symb "isString")
      [(mk_string_symb "sValue")] [Some ints_sort] [0] in
  let wasm_int_constructor =
    Datatype.mk_constructor ctx (mk_string_symb "Int") (mk_string_symb "isInt")
      [(mk_string_symb "iValue")] [Some ints_sort] [0] in

  let wasm_sort =
    Datatype.mk_sort
      ctx
      (mk_string_symb "WASM_Literal") 
      [
          wasm_bool_constructor;
          wasm_num_constructor;
          wasm_string_constructor;
          wasm_int_constructor 
      ] in

  try
    (*  Constructors  *)
    let z3_wasm_constructors = Datatype.get_constructors wasm_sort in
    let bool_constructor = List.nth z3_wasm_constructors 0 in
    let num_constructor = List.nth z3_wasm_constructors 1 in
    let string_constructor = List.nth z3_wasm_constructors 2 in
    let int_constructor = List.nth z3_wasm_constructors 3 in

    (*  Accessors  *)
    let z3_wasm_accessors = Datatype.get_accessors wasm_sort in
    let bool_accessor = List.nth (List.nth z3_wasm_accessors 0) 0 in
    let num_accessor = List.nth (List.nth z3_wasm_accessors 1) 0 in
    let string_accessor = List.nth (List.nth z3_wasm_accessors 2) 0 in
    let int_accessor = List.nth (List.nth z3_wasm_accessors 3) 0 in

    (*  Recognizers  *)
    let z3_wasm_recognizers = Datatype.get_recognizers wasm_sort in
    let bool_recognizer = List.nth z3_wasm_recognizers 0 in
    let num_recognizer = List.nth z3_wasm_recognizers 1 in
    let string_recognizer = List.nth z3_wasm_recognizers 2 in
    let int_recognizer = List.nth z3_wasm_recognizers 3 in

    let wasm_literal_operations   = {
      (*  Constructors  *)
      bool_constructor   = bool_constructor;
      num_constructor    = num_constructor;
      string_constructor = string_constructor;
      int_constructor    = int_constructor;

      (*  Accessors  *)
      bool_accessor      = bool_accessor;
      num_accessor       = num_accessor;
      string_accessor    = string_accessor;
      int_accessor       = int_accessor;

      (*  Recognizers  *)
      bool_recognizer    = bool_recognizer;
      num_recognizer     = num_recognizer;
      string_recognizer  = string_recognizer;
      int_recognizer     = int_recognizer
    }  in 
    wasm_sort, wasm_literal_operations
  with _ -> raise (Failure ("DEATH: construction of z3_wasm_sort"))

(*  String codes  *)
let str_codes     = Hashtbl.create 1000
let str_codes_inv = Hashtbl.create 1000
let str_counter   = ref 0

(*  Axiomatised operations --> for string length  *)
let axiomatised_operations =

  let slen_fun = FuncDecl.mk_func_decl ctx (mk_string_symb "s-len")
              [numbers_sort] numbers_sort in
  let bool_to_int = FuncDecl.mk_func_decl ctx (mk_string_symb "bool_to_int") 
              [booleans_sort] numbers_sort in
  {
    slen_fun = slen_fun;
    bool_to_int = bool_to_int;
  }

let bool_to_int_axioms =
  let z3_true   = Boolean.mk_true ctx in
  let z3_false  = Boolean.mk_false ctx in
  let true_app  = Expr.mk_app ctx axiomatised_operations.bool_to_int [z3_true] in
  let false_app = Expr.mk_app ctx axiomatised_operations.bool_to_int [z3_false] in
  let le        = Boolean.mk_eq ctx (mk_int_i 1) true_app in
  let le'       = Boolean.mk_eq ctx (mk_int_i 0) false_app in
  Boolean.mk_and ctx [le; le']

(*  Encode strings into integer values -> z3_code  *)
let encode_string (str: string) : Expr.expr =
  try
    let str_number = Hashtbl.find str_codes str in
    let z3_code = mk_int_i str_number in
    z3_code
  with Not_found ->
    (* New string: add it to the hashtable *)
    let z3_code = mk_int_i !str_counter in
    Hashtbl.add str_codes str (!str_counter);
    Hashtbl.add str_codes_inv (!str_counter) str;
    str_counter := !str_counter + 1;
    z3_code

(*  Encode values into Z3 expressions *)
let encode_val (v : Values.value) : Expr.expr = 
  match v with 
    | Values.I32 i -> 
      let sfn = Int32.to_string i in 
      let n_arg = mk_int_s sfn in
      Expr.mk_app ctx wasm_lit_operations.int_constructor [n_arg]

    | Values.I64 i ->
      let sfn = Int64.to_string i in 
      let n_arg = mk_int_s sfn in
      Expr.mk_app ctx wasm_lit_operations.int_constructor [n_arg]

    | Values.F32 f -> 
      let sfn = F32.to_string f in 
      let n_arg = mk_num_s sfn in
      Expr.mk_app ctx wasm_lit_operations.num_constructor [n_arg]

    | Values.F64 f -> 
      let sfn = F64.to_string f in 
      let n_arg = mk_num_s sfn in
      Expr.mk_app ctx wasm_lit_operations.num_constructor [n_arg]

let encode_val_bool (v : Values.value) : Expr.expr = 
  let z3_true   = Boolean.mk_true ctx in
  let z3_false  = Boolean.mk_false ctx in
  let true_app  = Expr.mk_app ctx wasm_lit_operations.bool_constructor [z3_true] in
  let false_app = Expr.mk_app ctx wasm_lit_operations.bool_constructor [z3_false] in
  match v with 
    | Values.I32 0l -> false_app
    | Values.I32 _  -> true_app
    | Values.I64 0L -> false_app
    | Values.I64 _  -> true_app
    | _ -> failwith "encoding float as a boolean value."

(* 
██╗███╗░░██╗████████╗  ██████╗░██████╗░
██║████╗░██║╚══██╔══╝  ╚════██╗╚════██╗
██║██╔██╗██║░░░██║░░░  ░█████╔╝░░███╔═╝
██║██║╚████║░░░██║░░░  ░╚═══██╗██╔══╝░░
██║██║░╚███║░░░██║░░░  ██████╔╝███████╗
╚═╝╚═╝░░╚══╝░░░╚═╝░░░  ╚═════╝░╚══════╝    *)

(*  Enconde int32 relative operations into Z3 expressions  *)
let encode_int32_relop (b_ctx : bool) op le1 le2 =
  (*  Relative operations between integers, that return a boolean  *)
  let binop_ints_to_booleans op le1 le2 =
    let le1' = (Expr.mk_app ctx wasm_lit_operations.int_accessor [le1]) in
    let le2' = (Expr.mk_app ctx wasm_lit_operations.int_accessor [le2]) in
    Expr.mk_app ctx wasm_lit_operations.bool_constructor [(op le1' le2')]
  in
  let mk_axiomatised_le_app op le1 le2 =
    let le1' = (Expr.mk_app ctx wasm_lit_operations.int_accessor [le1]) in
    let le2' = (Expr.mk_app ctx wasm_lit_operations.int_accessor [le2]) in
    Expr.mk_app ctx axiomatised_operations.bool_to_int [(op le1' le2')]
  in
  (match op, b_ctx with
    | Si32.I32Eq, true -> 
        Expr.mk_app ctx wasm_lit_operations.bool_constructor [(Boolean.mk_eq ctx le1 le2)]
    | Si32.I32Eq, false -> 
        let le = Boolean.mk_eq ctx le1 le2 in
        let le_app = Expr.mk_app ctx axiomatised_operations.bool_to_int [le] in
        Expr.mk_app ctx wasm_lit_operations.int_constructor [le_app]
    | Si32.I32Ne, true ->
      let le_b = Expr.mk_app ctx wasm_lit_operations.int_accessor [le1] in
      let le2_b = Expr.mk_app ctx wasm_lit_operations.int_accessor [le2] in
      let le = Boolean.mk_eq ctx le_b le2_b in 
      let n_le = Boolean.mk_not ctx le in
      Expr.mk_app ctx wasm_lit_operations.bool_constructor [n_le]
    | Si32.I32Ne, false ->
        let le = Boolean.mk_eq ctx le1 le2 in
        let le_neg = Boolean.mk_not ctx le in
        let le_app = Expr.mk_app ctx axiomatised_operations.bool_to_int [le_neg] in
        Expr.mk_app ctx wasm_lit_operations.int_constructor [le_app]
    | Si32.I32LtS, true ->
      binop_ints_to_booleans (mk_lt_i ctx) le1 le2
    | Si32.I32LtS, false ->
        let le_app = mk_axiomatised_le_app (mk_lt_i ctx) le1 le2 in
        Expr.mk_app ctx wasm_lit_operations.int_constructor [le_app]
    | Si32.I32LeS, true -> 
      binop_ints_to_booleans (mk_le_i ctx) le1 le2
    | Si32.I32LeS, false ->
        let le_app = mk_axiomatised_le_app (mk_le_i ctx) le1 le2 in
        Expr.mk_app ctx wasm_lit_operations.int_constructor [le_app]
    | Si32.I32GtS, true ->
      binop_ints_to_booleans (mk_gt_i ctx) le1 le2
    | Si32.I32GtS, false ->
        let le_app = mk_axiomatised_le_app (mk_gt_i ctx) le1 le2 in
        Expr.mk_app ctx wasm_lit_operations.int_constructor [le_app]
    | Si32.I32GeS, true ->
      binop_ints_to_booleans (mk_ge_i ctx) le1 le2
    | Si32.I32GeS, false ->
        let le_app = mk_axiomatised_le_app (mk_gt_i ctx) le1 le2 in
        Expr.mk_app ctx wasm_lit_operations.int_constructor [le_app])

(*  Encode int32 binary operations into Z3 expressions  *)
let encode_int32_binop (b_ctx : bool) op le1 le2 =
  (*  Binary operations between integers, that return an integer  *)
  let binop_ints_to_ints mk_op le1 le2 =
      let n_le1 = (Expr.mk_app ctx wasm_lit_operations.int_accessor [le1]) in
      let n_le2 = (Expr.mk_app ctx wasm_lit_operations.int_accessor [le2]) in
      let nle1_op_nle2 = mk_op n_le1 n_le2 in
      Expr.mk_app ctx wasm_lit_operations.int_constructor [nle1_op_nle2] in
  (*  According to the binary operation, perform the corresponding action  *)
  (match op with
    | Si32.I32Add -> 
      binop_ints_to_ints mk_add_i le1 le2

    | Si32.I32And -> 
      let le1_b = Expr.mk_app ctx wasm_lit_operations.bool_accessor [le1] in
      let le2_b = Expr.mk_app ctx wasm_lit_operations.bool_accessor [le2] in
      let le = Boolean.mk_and ctx [le1_b; le2_b] in 
      Expr.mk_app ctx wasm_lit_operations.bool_constructor [le]

    | Si32.I32Xor -> 
      let le1_b = Expr.mk_app ctx wasm_lit_operations.bool_accessor [le1] in
      let le2_b = Expr.mk_app ctx wasm_lit_operations.bool_accessor [le2] in
      let le = Boolean.mk_xor ctx le1_b le2_b in 
      Expr.mk_app ctx wasm_lit_operations.bool_constructor [le]

    | Si32.I32Or -> 
      let le1_b = Expr.mk_app ctx wasm_lit_operations.bool_accessor [le1] in
      let le2_b = Expr.mk_app ctx wasm_lit_operations.bool_accessor [le2] in
      let le = Boolean.mk_or ctx [le1_b; le2_b] in 
      Expr.mk_app ctx wasm_lit_operations.bool_constructor [le]

    | Si32.I32Sub -> 
      binop_ints_to_ints mk_sub_i le1 le2
    
    | Si32.I32Div -> 
      binop_ints_to_ints mk_div_i le1 le2

    | Si32.I32Mul -> 
      binop_ints_to_ints mk_mul_i le1 le2

    | Si32.I32Shl ->
      failwith "not encoded"
 
    | Si32.I32ShrS ->
      failwith "not encoded"
  )

(*  Encode int32 unary operations into Z3 expressions *)
let encode_int32_unop (b_ctx : bool) op le =
  raise (Failure (Printf.sprintf "SMT encoding: Construct not supported yet - unop"))


(* 
██╗███╗░░██╗████████╗  ░█████╗░░░██╗██╗
██║████╗░██║╚══██╔══╝  ██╔═══╝░░██╔╝██║
██║██╔██╗██║░░░██║░░░  ██████╗░██╔╝░██║
██║██║╚████║░░░██║░░░  ██╔══██╗███████║
██║██║░╚███║░░░██║░░░  ╚█████╔╝╚════██║
╚═╝╚═╝░░╚══╝░░░╚═╝░░░  ░╚════╝░░░░░░╚═╝     *)

(*  Enconde int64 relative operations into Z3 expressions  *)
let encode_int64_relop (b_ctx : bool) op le1 le2 =
  (*  Relative operations between integers, that return a boolean  *)
  let binop_ints_to_booleans mk_op le1 le2 =
    let n_le1 = (Expr.mk_app ctx wasm_lit_operations.int_accessor [le1]) in
    let n_le2 = (Expr.mk_app ctx wasm_lit_operations.int_accessor [le2]) in
    let nle1_op_nle2 = mk_op n_le1 n_le2 in
    Expr.mk_app ctx wasm_lit_operations.bool_constructor [nle1_op_nle2] in 

  (match op with
    | Si64.I64Eq -> 
      Expr.mk_app ctx wasm_lit_operations.bool_constructor [(Boolean.mk_eq ctx le1 le2)]

    | Si64.I64Ne ->
      let le_b = Expr.mk_app ctx wasm_lit_operations.int_accessor [le1] in
      let le2_b = Expr.mk_app ctx wasm_lit_operations.int_accessor [le2] in
      let le = Boolean.mk_eq ctx le_b le2_b in 
      let n_le = Boolean.mk_not ctx le in
      Expr.mk_app ctx wasm_lit_operations.bool_constructor [n_le]

    | Si64.I64Lt ->
      binop_ints_to_booleans (mk_lt_i ctx) le1 le2

    | Si64.I64Le -> 
      binop_ints_to_booleans (mk_le_i ctx) le1 le2

    | Si64.I64Gt ->
      binop_ints_to_booleans (mk_gt_i ctx) le1 le2

    | Si64.I64Ge ->
      binop_ints_to_booleans (mk_ge_i ctx) le1 le2
  )

(*  Encode int64 binary operations into Z3 expressions  *)
let encode_int64_binop (b_ctx : bool) op le1 le2 =
  (*  Binary operations between integers, that return an integer  *)
  let binop_ints_to_ints mk_op le1 le2 =
      let n_le1 = (Expr.mk_app ctx wasm_lit_operations.int_accessor [le1]) in
      let n_le2 = (Expr.mk_app ctx wasm_lit_operations.int_accessor [le2]) in
      let nle1_op_nle2 = mk_op n_le1 n_le2 in
      Expr.mk_app ctx wasm_lit_operations.int_constructor [nle1_op_nle2] in
  (*  According to the binary operation, perform the corresponding action  *)
  (match op with
    | Si64.I64Add -> 
      binop_ints_to_ints mk_add_i le1 le2

    | Si64.I64And -> 
      let le1_b = Expr.mk_app ctx wasm_lit_operations.bool_accessor [le1] in
      let le2_b = Expr.mk_app ctx wasm_lit_operations.bool_accessor [le2] in
      let le = Boolean.mk_and ctx [le1_b; le2_b] in 
      Expr.mk_app ctx wasm_lit_operations.bool_constructor [le]

    | Si64.I64Xor -> 
      let le1_b = Expr.mk_app ctx wasm_lit_operations.bool_accessor [le1] in
      let le2_b = Expr.mk_app ctx wasm_lit_operations.bool_accessor [le2] in
      let le = Boolean.mk_xor ctx le1_b le2_b in 
      Expr.mk_app ctx wasm_lit_operations.bool_constructor [le]

    | Si64.I64Or -> 
      let le1_b = Expr.mk_app ctx wasm_lit_operations.bool_accessor [le1] in
      let le2_b = Expr.mk_app ctx wasm_lit_operations.bool_accessor [le2] in
      let le = Boolean.mk_or ctx [le1_b; le2_b] in 
      Expr.mk_app ctx wasm_lit_operations.bool_constructor [le]

    | Si64.I64Sub -> 
      binop_ints_to_ints mk_sub_i le1 le2
    
    | Si64.I64Div -> 
      binop_ints_to_ints mk_div_i le1 le2

    | Si64.I64Mul -> 
      binop_ints_to_ints mk_mul_i le1 le2
  )

(*  Encode int64 unary operations into Z3 expressions *)
let encode_int64_unop (b_ctx : bool) op le =
  raise (Failure (Printf.sprintf "SMT encoding: Construct not supported yet - unop"))

(* 
███████╗██╗░░░░░░█████╗░░█████╗░████████╗  ██████╗░██████╗░
██╔════╝██║░░░░░██╔══██╗██╔══██╗╚══██╔══╝  ╚════██╗╚════██╗
█████╗░░██║░░░░░██║░░██║███████║░░░██║░░░  ░█████╔╝░░███╔═╝
██╔══╝░░██║░░░░░██║░░██║██╔══██║░░░██║░░░  ░╚═══██╗██╔══╝░░
██║░░░░░███████╗╚█████╔╝██║░░██║░░░██║░░░  ██████╔╝███████╗
╚═╝░░░░░╚══════╝░╚════╝░╚═╝░░╚═╝░░░╚═╝░░░  ╚═════╝░╚══════╝   *)

(*  Enconde float32 relative operations into Z3 expressions  *)
let encode_num32_relop (b_ctx : bool) op le1 le2 =
  (*  Relative operations between numbers, that return a boolean  *)
  let binop_nums_to_booleans mk_op le1 le2 =
    let n_le1 = (Expr.mk_app ctx wasm_lit_operations.num_accessor [le1]) in
    let n_le2 = (Expr.mk_app ctx wasm_lit_operations.num_accessor [le2]) in
    let nle1_op_nle2 = mk_op n_le1 n_le2 in
    Expr.mk_app ctx wasm_lit_operations.bool_constructor [nle1_op_nle2] in 

  (match op with
    | Sf32.F32Eq -> 
      Expr.mk_app ctx wasm_lit_operations.bool_constructor [(Boolean.mk_eq ctx le1 le2)]

    | Sf32.F32Ne ->
      let le_b = Expr.mk_app ctx wasm_lit_operations.num_accessor [le1] in
      let le2_b = Expr.mk_app ctx wasm_lit_operations.num_accessor [le2] in
      let le = Boolean.mk_eq ctx le_b le2_b in 
      let n_le = Boolean.mk_not ctx le in
      Expr.mk_app ctx wasm_lit_operations.bool_constructor [n_le]

    | Sf32.F32Lt ->
      binop_nums_to_booleans (mk_lt ctx) le1 le2

    | Sf32.F32Le -> 
      binop_nums_to_booleans (mk_le ctx) le1 le2

    | Sf32.F32Gt ->
      binop_nums_to_booleans (mk_gt ctx) le1 le2

    | Sf32.F32Ge ->
      binop_nums_to_booleans (mk_ge ctx) le1 le2
  )

(*  Encode float32 binary operations into Z3 expressions  *)
let encode_num32_binop (b_ctx : bool) op le1 le2 =
  (*  Binary operations between numbers, that return a number  *)
  let binop_nums_to_nums mk_op le1 le2 =
      let n_le1 = (Expr.mk_app ctx wasm_lit_operations.num_accessor [le1]) in
      let n_le2 = (Expr.mk_app ctx wasm_lit_operations.num_accessor [le2]) in
      let nle1_op_nle2 = mk_op n_le1 n_le2 in
      Expr.mk_app ctx wasm_lit_operations.num_constructor [nle1_op_nle2] in
  (*  According to the binary operation, perform the corresponding action  *)
  (match op with
    | Sf32.F32Add -> 
      binop_nums_to_nums mk_add le1 le2

    | Sf32.F32Sub -> 
      binop_nums_to_nums mk_sub le1 le2
    
    | Sf32.F32Div -> 
      binop_nums_to_nums mk_div le1 le2

    | Sf32.F32Mul -> 
      binop_nums_to_nums mk_mul le1 le2
  )

(*  Encode float32 unary operations into Z3 expressions *)
let encode_num32_unop (b_ctx : bool) op le =
  (match op with
    | Sf32.F32Neg -> 
      let le_n = Expr.mk_app ctx wasm_lit_operations.num_accessor [le] in
      let op_le_n = Arithmetic.mk_unary_minus ctx le_n in
      Expr.mk_app ctx wasm_lit_operations.num_constructor [op_le_n]
  )


(* 
███████╗██╗░░░░░░█████╗░░█████╗░████████╗  ░█████╗░░░██╗██╗
██╔════╝██║░░░░░██╔══██╗██╔══██╗╚══██╔══╝  ██╔═══╝░░██╔╝██║
█████╗░░██║░░░░░██║░░██║███████║░░░██║░░░  ██████╗░██╔╝░██║
██╔══╝░░██║░░░░░██║░░██║██╔══██║░░░██║░░░  ██╔══██╗███████║
██║░░░░░███████╗╚█████╔╝██║░░██║░░░██║░░░  ╚█████╔╝╚════██║
╚═╝░░░░░╚══════╝░╚════╝░╚═╝░░╚═╝░░░╚═╝░░░  ░╚════╝░░░░░░╚═╝    *)

(*  Enconde float64 relative operations into Z3 expressions  *)
let encode_num64_relop (b_ctx : bool) op le1 le2 =
  (*  Relative operations between numbers, that return a boolean  *)
  let binop_nums_to_booleans mk_op le1 le2 =
    let n_le1 = (Expr.mk_app ctx wasm_lit_operations.num_accessor [le1]) in
    let n_le2 = (Expr.mk_app ctx wasm_lit_operations.num_accessor [le2]) in
    let nle1_op_nle2 = mk_op n_le1 n_le2 in
    Expr.mk_app ctx wasm_lit_operations.bool_constructor [nle1_op_nle2] in 

  (match op with
    | Sf64.F64Eq -> 
      Expr.mk_app ctx wasm_lit_operations.bool_constructor [(Boolean.mk_eq ctx le1 le2)]

    | Sf64.F64Ne ->
      let le_b = Expr.mk_app ctx wasm_lit_operations.num_accessor [le1] in
      let le2_b = Expr.mk_app ctx wasm_lit_operations.num_accessor [le2] in
      let le = Boolean.mk_eq ctx le_b le2_b in 
      let n_le = Boolean.mk_not ctx le in
      Expr.mk_app ctx wasm_lit_operations.bool_constructor [n_le]

    | Sf64.F64Lt ->
      binop_nums_to_booleans (mk_lt ctx) le1 le2

    | Sf64.F64Le -> 
      binop_nums_to_booleans (mk_le ctx) le1 le2

    | Sf64.F64Gt ->
      binop_nums_to_booleans (mk_gt ctx) le1 le2

    | Sf64.F64Ge ->
      binop_nums_to_booleans (mk_ge ctx) le1 le2
  )

(*  Encode float64 binary operations into Z3 expressions  *)
let encode_num64_binop (b_ctx : bool) op le1 le2 =
  (*  Binary operations between numbers, that return a number  *)
  let binop_nums_to_nums mk_op le1 le2 =
      let n_le1 = (Expr.mk_app ctx wasm_lit_operations.num_accessor [le1]) in
      let n_le2 = (Expr.mk_app ctx wasm_lit_operations.num_accessor [le2]) in
      let nle1_op_nle2 = mk_op n_le1 n_le2 in
      Expr.mk_app ctx wasm_lit_operations.num_constructor [nle1_op_nle2] in
  (*  According to the binary operation, perform the corresponding action  *)
  (match op with
    | Sf64.F64Add -> 
      binop_nums_to_nums mk_add le1 le2

    | Sf64.F64Sub -> 
      binop_nums_to_nums mk_sub le1 le2
    
    | Sf64.F64Div -> 
      binop_nums_to_nums mk_div le1 le2

    | Sf64.F64Mul -> 
      binop_nums_to_nums mk_mul le1 le2
  )

(*  Encode float64 unary operations into Z3 expressions *)
let encode_num64_unop (b_ctx : bool) op le =
  (match op with
    | Sf64.F64Neg -> 
      let le_n = Expr.mk_app ctx wasm_lit_operations.num_accessor [le] in
      let op_le_n = Arithmetic.mk_unary_minus ctx le_n in
      Expr.mk_app ctx wasm_lit_operations.num_constructor [op_le_n]
  )

let is_boolean_binop binop : bool =
  match binop with
  | Si32.I32And
  | Si32.I32Xor
  | Si32.I32Or -> true
  | _ -> false


(*  Encode stack expressions (sym_value) into Z3 expressions *)
let rec encode_sym_val ?(bool_ctx=false) (e : Symvalue.sym_expr) : Expr.expr = 
  match e with 
  (* Value *)
  | Symvalue.Value v ->
      (match bool_ctx with
      | true -> encode_val_bool v
      | false -> encode_val v)
 (* I32 *)
  | Symvalue.I32Unop (op, e) ->
      let e' = encode_sym_val e in
      encode_int32_unop bool_ctx op e'
  | Symvalue.I32Binop (op, e1, e2) -> 
      let b = is_boolean_binop op in
      let e1' = encode_sym_val ~bool_ctx:b e1 in
      let e2' = encode_sym_val ~bool_ctx:b e2 in
      encode_int32_binop bool_ctx op e1' e2'
  | Symvalue.I32Relop (op, e1, e2) ->
      let e1' = encode_sym_val e1 in
      let e2' = encode_sym_val e2 in
      encode_int32_relop bool_ctx op e1' e2'
 (* I64 *)
  | Symvalue.I64Unop (op,e) -> 
      let e' = encode_sym_val e in
      encode_int64_unop bool_ctx op e'
  | Symvalue.I64Binop (op,e1,e2) -> 
      let e1' = encode_sym_val e1 in
      let e2' = encode_sym_val e2 in
      encode_int64_binop bool_ctx op e1' e2'
  | Symvalue.I64Relop (op,e1,e2) ->
      let e1' = encode_sym_val e1 in
      let e2' = encode_sym_val e2 in
      encode_int64_relop bool_ctx op e1' e2'
  (* F32 *)
  | Symvalue.F32Unop (op,e) ->
      let e' = encode_sym_val e in
      encode_num32_unop bool_ctx op e'
  | Symvalue.F32Binop (op,e1,e2) -> 
      let e1' = encode_sym_val e1 in
      let e2' = encode_sym_val e2 in
      encode_num32_binop bool_ctx op e1' e2'
  | Symvalue.F32Relop (op,e1,e2) ->
      let e1' = encode_sym_val e1 in
      let e2' = encode_sym_val e2 in
      encode_num32_relop bool_ctx op e1' e2'
  (* F64 *)
  | Symvalue.F64Unop (op,e) -> 
      let e' = encode_sym_val e in
      encode_num64_unop bool_ctx op e'
  | Symvalue.F64Binop (op,e1,e2) -> 
      let e1' = encode_sym_val e1 in
      let e2' = encode_sym_val e2 in
      encode_num64_binop bool_ctx op e1' e2'
  | Symvalue.F64Relop (op,e1,e2) ->
      let e1' = encode_sym_val e1 in
      let e2' = encode_sym_val e2 in
      encode_num64_relop bool_ctx op e1' e2'
  (* Symbolic *)
  | Symvalue.Symbolic (t, x) ->
      Expr.mk_const ctx (mk_string_symb x) z3_wasm_literal_sort


(**)
let make_recognizer_assertion (t_x : Symvalue.symbolic) (x : string) : Expr.expr =
  let le_x = Expr.mk_const ctx (mk_string_symb x) z3_wasm_literal_sort in
  match t_x with
    | Symvalue.SymInt32 -> Expr.mk_app ctx wasm_lit_operations.int_recognizer [ le_x ] 
    | Symvalue.SymInt64 -> Expr.mk_app ctx wasm_lit_operations.int_recognizer [ le_x ] 
    | Symvalue.SymFloat32 -> Expr.mk_app ctx wasm_lit_operations.num_recognizer [ le_x ] 
    | Symvalue.SymFloat64 -> Expr.mk_app ctx wasm_lit_operations.num_recognizer [ le_x ] 


(*  Top level function: encodes a path condition *)
let encode_top_level_expr (e : Symvalue.sym_value) : Expr.expr = 
  (*(if (not (Symvalue.is_boolean_expression e))
     then raise (Failure "encode_top_level_boolean_expr: non-boolean expression.")); 
  *) 
  let e_symbols : (string * Symvalue.symbolic) list = Symvalue.get_symbols e in 
  (* e_symbols = [ (#i1, int), (#i2, int) ] *)
  let e_symbol_types_exprs : Expr.expr list = 
    List.map (fun (x, t_x) -> make_recognizer_assertion t_x x) e_symbols in 
  (* [ isInt(#i1), isInt(#i2) ] *)
  let e_symbols_types_expr : Expr.expr = Boolean.mk_and ctx e_symbol_types_exprs in
  (* isInt(#i1) /\ isInt(#i2) -> Boolean.mk_and ctx [ a1; a2 ]  *)
  let e' : Expr.expr = encode_sym_val ~bool_ctx:true e in 
  let e_b : Expr.expr = Expr.mk_app ctx wasm_lit_operations.bool_accessor [e'] in
  (* e_b /\ isInt(#i1) /\ isInt(#i2) *)
  let e_b' : Expr.expr = Boolean.mk_and ctx [e_b; e_symbols_types_expr] in
  Boolean.mk_and ctx [e_b'; bool_to_int_axioms]

(*
  (#i1 + #i2 < 3) -> (#i1 + #i2 < 3) /\ isInt(#i1) /\ isInt(#i2)
*)
   


(*  Check the satisfiability of a list of path conditions (expressions). Returns a model.  *) 
let check_sat_core (es : Symvalue.path_conditions) : Model.model option =
  (if (es = [])
     then raise (Failure "check_sat_core: no path conditions were given."));  
  
  (* Step 1: Encode expressions *)
  let es' = List.map encode_top_level_expr es in

 (*(* Print expressions in solver *)
  let es_str = List.fold_left (fun acc b ->
    acc ^ (Expr.to_string b) ^ ";  "
  ) "" es'
  in Printf.printf "%s\n" es_str;
  *)

  (* Step 2: Reset the solver and add the encoded expressions *)
  let masterSolver = Solver.mk_solver ctx None in 
  Solver.add masterSolver es';
        
  (* Step 3: Check satisfiability *)
  let ret = Solver.check masterSolver [] in
  (*Printf.printf "The solver returned: %s\n" (Solver.string_of_status ret);*)
        
  (* Step 4: BREAK if ret = UNKNOWN *)
  if (ret = Solver.UNKNOWN) then (Printf.printf "\nThe solver has returned UNKNOWN. Exiting.....\n"; exit 1);

  (* Step 5: RETURN *)
  if (ret = Solver.SATISFIABLE) then (Solver.get_model masterSolver) else None


(*  Lift the model: Get a new symbolic store, according to the values previously used in the model  *)
let lift_z3_model (model : Model.model) (sym_int32 : string list) (sym_int64 : string list) (sym_float32 : string list) (sym_float64 : string list) = 

  (*  Recover numbers  *)
  let recover_z3_number (n : Expr.expr) : float option = 
    if (Expr.is_numeral n) then (
      (*Printf.printf "Z3 number: %s\n"  (Expr.to_string n);*)
      Some (float_of_string (Arithmetic.Real.to_decimal_string n 16))
    ) else None in  
  
  (*  Recover integers  *)
  let recover_z3_int (zn : Expr.expr) : int option =  
    let n = recover_z3_number zn in 
    Option.map int_of_float n in 

  (*  Lift integer values  *)
  let lift_z3_val_int32 (x : string) : Values.value option = 
    let x'  = encode_sym_val (Symvalue.Symbolic (Symvalue.SymInt32, x)) in 
    let x'' = Expr.mk_app ctx wasm_lit_operations.int_accessor [(x')] in 
    let v   = Model.eval model x'' true in
    let n   = Option.map_default recover_z3_int None v in 
    Option.map (fun x -> Values.I32 (Int32.of_int x)) n 
    in

  (*  Lift integer values  *)
  let lift_z3_val_int64 (x : string) : Values.value option = 
    let x'  = encode_sym_val (Symvalue.Symbolic (Symvalue.SymInt64, x)) in 
    let x'' = Expr.mk_app ctx wasm_lit_operations.int_accessor [(x')] in 
    let v   = Model.eval model x'' true in
    let n   = Option.map_default recover_z3_int None v in 
    Option.map (fun x -> Values.I64 (Int64.of_int x)) n 
    in

  (*  Lift float values  *)
  let lift_z3_val_float32 (x : string) : Values.value option = 
    let x'  = encode_sym_val (Symvalue.Symbolic (Symvalue.SymFloat32, x)) in 
    let x'' = Expr.mk_app ctx wasm_lit_operations.num_accessor [(x')] in 
    let v   = Model.eval model x'' true in
    let n   = Option.map_default recover_z3_number None v in 
    Option.map (fun x -> Values.F32 (F32.of_float x)) n 
    in

  (*  Lift float values  *)
  let lift_z3_val_float64 (x : string) : Values.value option = 
    let x'  = encode_sym_val (Symvalue.Symbolic (Symvalue.SymFloat64, x)) in 
    let x'' = Expr.mk_app ctx wasm_lit_operations.num_accessor [(x')] in 
    let v   = Model.eval model x'' true in
    let n   = Option.map_default recover_z3_number None v in 
    Option.map (fun x -> Values.F64 (F64.of_float x)) n 
    in

  (*  The new symbolic store  *)
  (*  Add integer values to the store  *) 
  let i32_binds = 
  List.fold_left
    (fun a x -> 
      let v = lift_z3_val_int32 x in 
      (*Printf.printf "Z3 binding for %s: %s\n" x (Option.map_default Values.string_of_value "NO BINDING!" v); *)
      Option.map_default (fun y -> (x, y) :: a) (a) v   
    ) [] sym_int32
  in
  let i64_binds =
  List.fold_left
    (fun a x -> 
      let v = lift_z3_val_int64 x in 
      (*Printf.printf "Z3 binding for %s: %s\n" x (Option.map_default Values.string_of_value "NO BINDING!" v); *)
      Option.map_default (fun y -> (x, y) :: a) (a) v   
    ) [] sym_int64
  in
  let f32_binds =
  List.fold_left
    (fun a x -> 
      let v = lift_z3_val_float32 x in 
      (*Printf.printf "Z3 binding for %s: %s\n" x (Option.map_default Values.string_of_value "NO BINDING!" v); *)
      Option.map_default (fun y -> (x, y) :: a) (a) v   
    ) [] sym_float32 
  in
  let f64_binds =
  List.fold_left
    (fun a x -> 
      let v = lift_z3_val_float64 x in 
      (*Printf.printf "Z3 binding for %s: %s\n" x (Option.map_default Values.string_of_value "NO BINDING!" v); *)
      Option.map_default (fun y -> (x, y) :: a) (a) v   
    ) [] sym_float64
  in
  i32_binds @ (i64_binds @ (f32_binds @ f64_binds))


