open Si32
open Si64
open Sf32
open Sf64
open Symvalue

(*  Evaluate a test operation  *)
let eval_testop (s1 : sym_value) (op : Ast.testop) : sym_value =
	let (v, se) = s1 in 
	let v' = Values.value_of_bool (Eval_numeric.eval_testop op v) in
	let se' = 
		(match se with
    | Value _ -> Value v'
		| _ -> 
        (match op with
				| Values.I32 Ast.I32Op.Eqz -> I32Relop (I32Eq, se, Value (Values.I32 (Int32.of_int 0)))
				| Values.I64 Ast.I64Op.Eqz -> I64Relop (I64Eq, se, Value (Values.I64 (Int64.of_int 0)))
				| _ -> failwith "Operation not supported yet"))
  in (v', se')

(*  Evaluate a unary operation  *)
let eval_unop (s1 : sym_value) (op : Ast.unop) : sym_value =
	let (v, se) = s1 in 
	let v' = Eval_numeric.eval_unop op v in
	let se' = 
		(match se with
    | Value _ -> Value v'
	  | _ -> 
        (match op with
				| Values.F32 Ast.F32Op.Neg -> F32Unop (F32Neg, se)
				| Values.F64 Ast.F64Op.Neg -> F64Unop (F64Neg, se)
				| _ -> failwith "Operation not supported yet")) 
  in (v', se')

(*  Evaluate a binary operation *) 
let eval_binop (s1 : sym_value) (s2 : sym_value) (op : Ast.binop) : sym_value =
	let (v1, se1) = s1 in
	let (v2, se2) = s2 in 
  Printf.printf "(v1, se1)=(%s, %s), (v2, se2)=(%s, %s)" (Values.string_of_value v1) (pp_to_string se1) (Values.string_of_value v2) (pp_to_string se2);
	let v' = Eval_numeric.eval_binop op v1 v2 in
  Printf.printf " result=%s" (Values.string_of_value v');
	let se' = 
    begin match se1, se2 with
    | Value _, Value _ -> Value v'
		| _ -> 
        begin match op with
			  (* I32 *)
			  | Values.I32 Ast.I32Op.Add  -> I32Binop (I32Add , se1, se2)
				| Values.I32 Ast.I32Op.And  -> I32Binop (I32And , se1, se2)
				| Values.I32 Ast.I32Op.Or   -> I32Binop (I32Or  , se1, se2)
        | Values.I32 Ast.I32Op.Sub  -> I32Binop (I32Sub , se1, se2)
				| Values.I32 Ast.I32Op.DivS -> I32Binop (I32DivS, se1, se2)
				| Values.I32 Ast.I32Op.DivU -> I32Binop (I32DivU, se1, se2)
				| Values.I32 Ast.I32Op.Xor  -> I32Binop (I32Xor , se1, se2)
				| Values.I32 Ast.I32Op.Mul  -> I32Binop (I32Mul , se1, se2)
        | Values.I32 Ast.I32Op.Shl  -> I32Binop (I32Shl , se1, se2)
        | Values.I32 Ast.I32Op.ShrS -> I32Binop (I32ShrS, se1, se2)
        | Values.I32 Ast.I32Op.ShrU -> I32Binop (I32ShrU, se1, se2)
        | Values.I32 _ -> failwith "I32 binop not implemented"
				(* I64 *)
				| Values.I64 Ast.I64Op.Add  -> I64Binop (I64Add, se1, se2)
				| Values.I64 Ast.I64Op.And  -> I64Binop (I64And, se1, se2)
				| Values.I64 Ast.I64Op.Or   -> I64Binop (I64Or , se1, se2)
				| Values.I64 Ast.I64Op.Sub  -> I64Binop (I64Sub, se1, se2)
				| Values.I64 Ast.I64Op.DivS -> I64Binop (I64Div, se1, se2)
				| Values.I64 Ast.I64Op.Xor  -> I64Binop (I64Xor, se1, se2)
				| Values.I64 Ast.I64Op.Mul  -> I64Binop (I64Mul, se1, se2)
        | Values.I64 _ -> failwith "I64 binop not implemented"
				(* F32 *)
				| Values.F32 Ast.F32Op.Add  -> F32Binop (F32Add, se1, se2)
				| Values.F32 Ast.F32Op.Sub  -> F32Binop (F32Sub, se1, se2)
				| Values.F32 Ast.F32Op.Div  -> F32Binop (F32Div, se1, se2)
				| Values.F32 Ast.F32Op.Mul  -> F32Binop (F32Mul, se1, se2)
				| Values.F32 _ -> failwith "F32 binop not implemented"
				(* F64 *)
				| Values.F64 Ast.F64Op.Add  -> F64Binop (F64Add, se1, se2)
				| Values.F64 Ast.F64Op.Sub  -> F64Binop (F64Sub, se1, se2)
				| Values.F64 Ast.F64Op.Div  -> F64Binop (F64Div, se1, se2)
				| Values.F64 Ast.F64Op.Mul  -> F64Binop (F64Mul, se1, se2)
				| Values.F64 _ -> failwith "F64 binop not implemented"
        end
    end
  in (v', se')

(*  Evaluate a relative operation  *)
let eval_relop (s1 : sym_value) (s2 : sym_value) (op : Ast.relop) : sym_value =
	let (v1, se1) = s1
  and (v2, se2) = s2 in 
	let v' = Values.value_of_bool (Eval_numeric.eval_relop op v1 v2) in
	let se' = 
    begin match se1,se2 with
    | Value _, Value _ -> Value v'
		| _ -> 
        begin match op with
				(* I32 *)
        | Values.I32 Ast.I32Op.Eq  -> I32Relop (I32Eq , se1, se2)
				| Values.I32 Ast.I32Op.Ne  -> I32Relop (I32Ne , se1, se2)
				| Values.I32 Ast.I32Op.LtU -> I32Relop (I32LtU, se1, se2)
				| Values.I32 Ast.I32Op.LtS -> I32Relop (I32LtS, se1, se2)
				| Values.I32 Ast.I32Op.GtU -> I32Relop (I32GtU, se1, se2)
				| Values.I32 Ast.I32Op.GtS -> I32Relop (I32GtS, se1, se2)
				| Values.I32 Ast.I32Op.LeU -> I32Relop (I32LeU, se1, se2)
				| Values.I32 Ast.I32Op.LeS -> I32Relop (I32LeS, se1, se2)
				| Values.I32 Ast.I32Op.GeU -> I32Relop (I32GeU, se1, se2)
				| Values.I32 Ast.I32Op.GeS -> I32Relop (I32GeS, se1, se2)
				(* I64 *)					  
				| Values.I64 Ast.I64Op.Eq  -> I64Relop (I64Eq , se1, se2)
				| Values.I64 Ast.I64Op.Ne  -> I64Relop (I64Ne , se1, se2)
				| Values.I64 Ast.I64Op.LtU -> I64Relop (I64LtU, se1, se2)
				| Values.I64 Ast.I64Op.LtS -> I64Relop (I64LtS, se1, se2)
				| Values.I64 Ast.I64Op.GtU -> I64Relop (I64GtU, se1, se2)
				| Values.I64 Ast.I64Op.GtS -> I64Relop (I64GtS, se1, se2)
				| Values.I64 Ast.I64Op.LeU -> I64Relop (I64LeU, se1, se2)
				| Values.I64 Ast.I64Op.LeS -> I64Relop (I64LeS, se1, se2)
				| Values.I64 Ast.I64Op.GeU -> I64Relop (I64GeU, se1, se2)
				| Values.I64 Ast.I64Op.GeS -> I64Relop (I64GeS, se1, se2)
				(* F32 *)
				| Values.F32 Ast.F32Op.Eq  -> F32Relop (F32Eq, se1, se2)
				| Values.F32 Ast.F32Op.Ne  -> F32Relop (F32Ne, se1, se2)
				| Values.F32 Ast.F32Op.Lt  -> F32Relop (F32Lt, se1, se2)
				| Values.F32 Ast.F32Op.Gt  -> F32Relop (F32Gt, se1, se2)
				| Values.F32 Ast.F32Op.Le  -> F32Relop (F32Le, se1, se2)
				| Values.F32 Ast.F32Op.Ge  -> F32Relop (F32Ge, se1, se2)
				(* F64 *)					  
				| Values.F64 Ast.F64Op.Eq  -> F64Relop (F64Eq, se1, se2)
				| Values.F64 Ast.F64Op.Ne  -> F64Relop (F64Ne, se1, se2)
				| Values.F64 Ast.F64Op.Lt  -> F64Relop (F64Lt, se1, se2)
				| Values.F64 Ast.F64Op.Gt  -> F64Relop (F64Gt, se1, se2)
				| Values.F64 Ast.F64Op.Le  -> F64Relop (F64Le, se1, se2)
				| Values.F64 Ast.F64Op.Ge  -> F64Relop (F64Ge, se1, se2)
        end
    end
  in (v', se')
