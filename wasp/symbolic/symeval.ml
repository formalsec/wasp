
(*
░██████╗██╗░░░██╗███╗░░░███╗  ███████╗██╗░░░██╗░█████╗░██╗░░░░░
██╔════╝╚██╗░██╔╝████╗░████║  ██╔════╝██║░░░██║██╔══██╗██║░░░░░
╚█████╗░░╚████╔╝░██╔████╔██║  █████╗░░╚██╗░██╔╝███████║██║░░░░░
░╚═══██╗░░╚██╔╝░░██║╚██╔╝██║  ██╔══╝░░░╚████╔╝░██╔══██║██║░░░░░
██████╔╝░░░██║░░░██║░╚═╝░██║  ███████╗░░╚██╔╝░░██║░░██║███████╗
╚═════╝░░░░╚═╝░░░╚═╝░░░░░╚═╝  ╚══════╝░░░╚═╝░░░╚═╝░░╚═╝╚══════╝   *)

open Values
open Symvalue
open Types
open Instance
open Ast
open Source
open Logicenv
open Evaluations
open Si32

(* Errors *)

module Link = Error.Make ()
module Trap = Error.Make ()
module Crash = Error.Make ()
module Exhaustion = Error.Make ()

exception Link = Link.Error
exception Trap = Trap.Error
exception Crash = Crash.Error (* failure that cannot happen in valid code *)
exception Exhaustion = Exhaustion.Error

let memory_error at = function
  | Symmem2.InvalidAddress -> "address not found in hashtable"
  | Symmem2.Bounds -> "out of bounds memory access"
  (* TODO: might just remove these *)
  | Memory.SizeOverflow -> "memory size overflow"
  | Memory.SizeLimit -> "memory size limit reached"
  | Memory.Type -> Crash.error at "type mismatch at memory access"
  | exn -> raise exn

let numeric_error at = function
  | Numeric_error.IntegerOverflow -> "integer overflow"
  | Numeric_error.IntegerDivideByZero -> "integer divide by zero"
  | Numeric_error.InvalidConversionToInteger -> "invalid conversion to integer"
  | Eval_numeric.TypeError (i, v, t) ->
    Crash.error at
      ("type error, expected " ^ Types.string_of_value_type t ^ " as operand " ^
       string_of_int i ^ ", got " ^ Types.string_of_value_type (Values.type_of v))
  | exn -> raise exn


(* Administrative Expressions & Configurations *)

type 'a stack = 'a list

(*  Symbolic Frame  *)
type sym_frame =
{
  sym_inst : module_inst;
  sym_locals : sym_value ref list; (*  Locals can be symbolic  *)
}

(*  Symbolic code  *)
type sym_code = sym_value stack * sym_admin_instr list

and sym_admin_instr = sym_admin_instr' phrase
and sym_admin_instr' =
  | SPlain of instr'
  | SInvoke of func_inst
  | STrapping of string
  | SReturning of sym_value stack 
  | SBreaking of int32 * sym_value stack
  | SLabel of int * instr list * sym_code
  | SFrame of int * sym_frame * sym_code


(*  Symbolic configuration  *)
type sym_config =
{
  sym_frame : sym_frame;
  sym_code : sym_code;
  mutable logic_env : logical_env;
  path_cond : path_conditions;
  mutable sym_mem : Symmem2.t;
  sym_budget : int;  (* to model stack overflow *)
}

(*  Symbolic frame and configuration  *)
let sym_frame sym_inst sym_locals = {sym_inst; sym_locals}
let sym_config inst vs es sym_m = {
  sym_frame = sym_frame inst []; 
  sym_code = vs, es; 
  logic_env = (create_logic_env []);
  path_cond = [];
  sym_mem = sym_m;
  sym_budget = 300
}

(* AssertFail finish flag *)
let finish = ref false

(* To keep track of in which iteration the execution is in *)
let iterations = ref 1

(* To keep track of the coverage of the test *)
let lines = ref []
let lines_total = ref []

(* AssertFail constraint list *)
let finish_constraints = Constraints.create_constraints

let plain e = SPlain e.it @@ e.at

let lookup category list x =
  try Lib.List32.nth list x.it with Failure _ ->
    Crash.error x.at ("undefined " ^ category ^ " " ^ Int32.to_string x.it)

let type_ (inst : module_inst) x = lookup "type" inst.types x
let func (inst : module_inst) x = lookup "function" inst.funcs x
let table (inst : module_inst) x = lookup "table" inst.tables x
let memory (inst : module_inst) x = lookup "memory" inst.memories x
let global (inst : module_inst) x = lookup "global" inst.globals x
let local (frame : sym_frame) x = lookup "local" frame.sym_locals x

let elem inst x i at =
  match Table.load (table inst x) i with
  | Table.Uninitialized ->
    Trap.error at ("uninitialized element " ^ Int32.to_string i)
  | f -> f
  | exception Table.Bounds ->
    Trap.error at ("undefined element " ^ Int32.to_string i)

let func_elem inst x i at =
  match elem inst x i at with
  | FuncElem f -> f
  | _ -> Crash.error at ("type mismatch for element " ^ Int32.to_string i)

let take n (vs : 'a stack) at =
  try Lib.List.take n vs with Failure _ -> Crash.error at "stack underflow"

let drop n (vs : 'a stack) at =
  try Lib.List.drop n vs with Failure _ -> Crash.error at "stack underflow"

(* Evaluation *)
(*
 * Conventions:
 *   e  : instr
 *   v  : value
 *   es : instr list
 *   vs : value stack --> (Value i, sym_value)
 *   c : config
 *)

let instr_str e =
    match e with
    | Unreachable -> "unreachable"
    | Nop -> "nop"
    | Drop -> "drop"
    | Select -> "select"
    | Block (ts, es) -> "block"
    | Loop (ts, es) -> "loop"
    | If (ts, es1, es2) ->
      "if"
    | Br x -> "br " 
    | BrIf x -> "br_if "
    | BrTable (xs, x) ->
      "br_table "
    | Return -> "return"
    | Call x -> "call "
    | CallIndirect x -> "call_indirect"
    | LocalGet x -> "local.get "
    | LocalSet x -> "local.set "
    | LocalTee x -> "local.tee "
    | GlobalGet x -> "global.get "
    | GlobalSet x -> "global.set "
    | Load op -> "load"
    | Store op -> "store"
    | MemorySize -> "memory.size"
    | MemoryGrow -> "memory.grow"
    | Const lit -> "const"
    | Test op -> "test"
    | Compare op -> "cmp"
    | Unary op -> "unary"
    | Binary op -> "binary"
    | Convert op -> "convert"
    | _ -> "not support"

let fresh_sth (name : string) : (unit -> string) =
  let counter = ref 0 in
  let f () =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f

let fresh_sym_var : (unit -> string) =
  fresh_sth "#DVAR"

(*  Symbolic step  *)
let rec sym_step (c : sym_config) : sym_config =
  let {sym_frame = frame; sym_code = vs, es; logic_env; path_cond; sym_mem; _} = c in
  let e = List.hd es in
  if not (List.memq (Source.get_line e.at) !lines) then
    lines := !lines @ [(Source.get_line e.at)];
  if not (List.memq (Source.get_line e.at) !lines_total) then 
    lines_total := !lines_total @ [(Source.get_line e.at)];
  let vs', es', logic_env', path_cond', sym_mem' =
    match e.it, vs with
    | SPlain e', vs -> 
      (*Printf.printf ("\n Instr: %s\nStack:\n %s\n##################################################\n\n") (instr_str e') (Symvalue.print_c_sym_values vs);*)
      (match e', vs with
      | Unreachable, vs ->
        vs, [STrapping "unreachable executed" @@ e.at], logic_env, path_cond, sym_mem

      | Nop, vs ->
        vs, [], logic_env, path_cond, sym_mem

      | Block (ts, es'), vs ->
        vs, [SLabel (List.length ts, [], ([], List.map plain es')) @@ e.at], logic_env, path_cond, sym_mem

      | Loop (ts, es'), vs ->
        vs, [SLabel (0, [e' @@ e.at], ([], List.map plain es')) @@ e.at], logic_env, path_cond, sym_mem

      | If (ts, es1, es2), (I32 0l, ex) :: vs' -> 
        let ex' = simplify ex in
        let to_add =
          begin match ex with
          | Value _ -> []
          | _       -> 
              let ex'' =
                if not (is_relop ex') then I32Relop (I32Ne, ex', Value (I32 0l))
                else ex'
              in [neg_expr ex'']
          end
        in
        (*Printf.printf ("\n\n###### Entered IF, with 0 on top of stack. ######\nPath conditions are now:\n %s\n#################################################\n\n")   (Symvalue.str_path_cond ([v'] @ path_cond));*)
        vs', [SPlain (Block (ts, es2)) @@ e.at], logic_env, to_add @ path_cond, sym_mem

      | If (ts, es1, es2), (I32 i, ex) :: vs' -> 
        let ex' = simplify ex in
        let to_add =
          begin match ex' with
          | Value _ -> []
          | _ ->
              let ex'' = 
                if not (is_relop ex') then I32Relop (I32Ne, ex', Value (I32 0l))
                else ex'
              in [ex'']
          end
        in
        (*Printf.printf ("\n\n###### Entered IF, with !=0 on top of stack. ######\nPath conditions are now:\n %s\n##################################################\n\n")   (Symvalue.str_path_cond ([v'] @ path_cond));*)
        vs', [SPlain (Block (ts, es1)) @@ e.at], logic_env, to_add @ path_cond, sym_mem

      | Br x, vs ->
        [], [SBreaking (x.it, vs) @@ e.at], logic_env, path_cond, sym_mem

      | BrIf x, (I32 0l, ex) :: vs' ->
        let ex' = simplify ex in
        let to_add =
          begin match ex' with
          | Value _ -> []
          | _ ->
              let ex'' = 
                if not (is_relop ex') then I32Relop (I32Ne, ex', Value (I32 0l))
                else ex'
              in [neg_expr ex'']
          end
        in
        (*Printf.printf ("\n\n###### Entered BRIF, with 0 on top of stack @ (%s) ######\nPath conditions are now:\n %s\n#################################################\n\n") (Source.string_of_region e.at) (Symvalue.pp_string_of_pc
         (to_add @ path_cond));*)
        vs', [], logic_env, to_add @ path_cond, sym_mem

      | BrIf x, (I32 i, ex) :: vs' -> 
        let ex' = simplify ex in
        let to_add = 
          begin match ex' with
          | Value _ -> []
          | _ ->
              let ex'' = 
                if not (is_relop ex') then I32Relop (I32Ne, ex', Value (I32 0l))
                else ex'
              in [ex'']
          end
        in
        (*Printf.printf ("\n\n###### Entered IF, with !=0 on top of stack @ (%s) ######\nPath conditions are now:\n %s\n##################################################\n\n") (Source.string_of_region e.at) (Symvalue.pp_string_of_pc (to_add @ path_cond));*)
        vs', [SPlain (Br x) @@ e.at], logic_env, to_add @ path_cond, sym_mem

      | BrTable (xs, x), (I32 i, _) :: vs' when I32.ge_u i (Lib.List32.length xs) ->
        vs', [SPlain (Br x) @@ e.at], logic_env, path_cond, sym_mem

      | BrTable (xs, x), (I32 i, _) :: vs' ->
        vs', [SPlain (Br (Lib.List32.nth xs i)) @@ e.at], logic_env, path_cond, sym_mem

      | Return, vs ->
        [], [SReturning vs @@ e.at], logic_env, path_cond, sym_mem

      | Call x, vs ->
        vs, [SInvoke (func frame.sym_inst x) @@ e.at], logic_env, path_cond, sym_mem

      | CallIndirect x, (I32 i, _) :: vs ->
        let func = func_elem frame.sym_inst (0l @@ e.at) i e.at in
        if type_ frame.sym_inst x <> Func.type_of func then
          vs, [STrapping "indirect call type mismatch" @@ e.at], logic_env, path_cond, sym_mem
        else
          vs, [SInvoke func @@ e.at], logic_env, path_cond, sym_mem

      | Drop, v :: vs' ->
        vs', [], logic_env, path_cond, sym_mem

      | Select, (I32 0l, _) :: v2 :: v1 :: vs' ->
        v2 :: vs', [], logic_env, path_cond, sym_mem

      | Select, (I32 i, _) :: v2 :: v1 :: vs' ->
        v1 :: vs', [], logic_env, path_cond, sym_mem

      | LocalGet x, vs ->
        !(local frame x) :: vs, [], logic_env, path_cond, sym_mem

      | LocalSet x, v :: vs' ->
        local frame x := v;
        vs', [], logic_env, path_cond, sym_mem 

      | LocalTee x, v :: vs' ->
        local frame x := v;
        v :: vs', [], logic_env, path_cond, sym_mem

      | GlobalGet x, vs ->
        let v' = Global.load (global frame.sym_inst x) in
        (v', Value v') :: vs, [], logic_env, path_cond, sym_mem

      | GlobalSet x, (v, _) :: vs' ->
        (try 
          Global.store (global frame.sym_inst x) v; vs', [], logic_env, path_cond, sym_mem
        with  Global.NotMutable -> Crash.error e.at "write to immutable global"
            | Global.Type -> Crash.error e.at "type mismatch at global write")

      | Load {offset; ty; sz; _}, (I32 i, _) :: vs' -> 
        (* let mem = memory frame.sym_inst (0l @@ e.at) in *)
        let base = I64_convert.extend_i32_u i in
        begin try
          let (v, e) =
            match sz with
            | None -> Symmem2.load_value sym_mem base offset ty
            | Some (sz, ext) -> Symmem2.load_packed sz sym_mem base offset ty
          in (v, e) :: vs', [], logic_env, path_cond, sym_mem
        with exn -> vs', [STrapping (memory_error e.at exn) @@ e.at], logic_env, path_cond, sym_mem end

      | Store {offset; sz; _}, (v, ex) :: (I32 i, _) :: vs' ->
        (*let mem = memory frame.sym_inst (0l @@ e.at) in*)
        let base = I64_convert.extend_i32_u i in
        begin try
          begin match sz with
          | None -> Symmem2.store_value sym_mem base offset (v, ex)
          | Some sz -> Symmem2.store_packed sz sym_mem base offset (v, ex)
          end;
          vs', [], logic_env, path_cond, sym_mem
        with exn -> vs', [STrapping (memory_error e.at exn) @@ e.at], logic_env, path_cond, sym_mem end
        (*
        (try
          (match sz with
          | None -> 
              Memory.store_value mem base offset v; 
              Symmem2.store_value sym_mem base offset (v, ex)
          | Some sz -> 
              Memory.store_packed sz mem base offset v; (* assert (packed_size sz <= Types.size (Values.type_of v)); *)
              (*Symmem.store_value sym_mem (Int64.to_int addr) (v, ex, (Memory.packed_size sz));*)
              Symmem2.store_packed sz sym_mem base offset (v, ex)
          );
          vs', [], logic_env, path_cond, sym_mem
        with 
          | Failure f -> Crash.error e.at f
          | exn -> vs', [STrapping (memory_error e.at exn) @@ e.at], logic_env, path_cond, sym_mem)

      *)
      | MemorySize, vs ->
        let mem = memory frame.sym_inst (0l @@ e.at) in
        (I32 (Memory.size mem), Value (I32 (Memory.size mem))) :: vs, [], logic_env, path_cond, sym_mem

      | MemoryGrow, (I32 delta, _) :: vs' ->
        let mem = memory frame.sym_inst (0l @@ e.at) in
        let old_size = Memory.size mem in
        let result =
          try Memory.grow mem delta; old_size
          with Memory.SizeOverflow | Memory.SizeLimit | Memory.OutOfMemory -> -1l
        in (I32 result, Value (I32 result)) :: vs', [], logic_env, path_cond, sym_mem

      | Const v, vs ->
        (v.it, Value (v.it)) :: vs, [], logic_env, path_cond, sym_mem

      | Test testop, v :: vs' ->
        (try 
          let new_conf = eval_testop v testop in
          new_conf :: vs', [], logic_env, path_cond, sym_mem
        with exn -> vs', [STrapping (numeric_error e.at exn) @@ e.at], logic_env, path_cond, sym_mem)

      | Compare relop, v2 :: v1 :: vs' ->
        (try
          let new_conf = eval_relop v1 v2 relop in
          new_conf :: vs', [], logic_env, path_cond, sym_mem
        with exn -> vs', [STrapping (numeric_error e.at exn) @@ e.at], logic_env, path_cond, sym_mem)

      | Unary unop, v :: vs' ->
        (try 
          let new_conf = eval_unop v unop in
          new_conf :: vs', [], logic_env, path_cond, sym_mem
        with exn -> vs', [STrapping (numeric_error e.at exn) @@ e.at], logic_env, path_cond, sym_mem)

      | Binary binop, v2 :: v1 :: vs' ->
        (try 
          let new_conf = eval_binop v1 v2 binop in
          new_conf :: vs', [], logic_env, path_cond, sym_mem
        with exn -> vs', [STrapping (numeric_error e.at exn) @@ e.at], logic_env, path_cond, sym_mem)

      | Convert cvtop, (v,_) :: vs' ->
        (try 
          let v' = Eval_numeric.eval_cvtop cvtop v in 
          (v', Value v'):: vs', [], logic_env, path_cond, sym_mem
        with exn -> vs', [STrapping (numeric_error e.at exn) @@ e.at], logic_env, path_cond, sym_mem)

      | Dup, v :: vs' ->
        v :: v :: vs', [], logic_env, path_cond, sym_mem
      
      | SymAssert, (I32 i, ex) :: vs' -> (* != 0 on top of stack *)
        Printf.printf "%s\n" (pp_string_of_pc path_cond);
        Printf.printf ">>> Assert reached. Checking satisfiability...\n";
        let ex' = Symvalue.simplify ex in
        Printf.printf "simplify (%s) = %s\n" (pp_to_string ex) (pp_to_string ex');
        begin match ex' with 
        | Value (I32 0l) ->
            Crash.error e.at (
              "\n******* Asserted false *******\n" ^ 
              "Path conditions are:\n"             ^ (pp_string_of_pc path_cond) ^ 
              "\n\nLogical environment is:\n"      ^ (print_sym_store logic_env) ^ 
              "\n******************************\n\n")
        | Value (I32 1l) ->
            Printf.printf "\n\n###### Assertion passed ######\n";
            vs', [], logic_env, path_cond, sym_mem
        | _ ->
          let query = neg_expr ex' in
          Printf.printf "Query: %s\n" (pp_to_string query);
          if (path_cond = []) then begin
            Printf.printf "\n\n###### Assertion passed ######\n";
            vs', [], logic_env, path_cond, sym_mem
          end else begin
            begin match Z3Encoding2.check_sat_core [and_list (path_cond @ [query])] with 
            | None -> (* Not satisfiable, execution can continue *)
                Printf.printf "\n\n###### Assertion passed ######\n";
                vs', [], logic_env, path_cond, sym_mem
            | Some m -> (* Satisfiable, exception raised *)
                Crash.error e.at (
                  "\n****** Assertion failed ******" ^
                  "\nModel is:\n"                    ^ (Z3.Model.to_string m) ^ 
                  "\n******************************\n\n")
            end
          end
        end

      | SymAssume, (I32 0l, ex) :: vs' ->
        Printf.printf ">>> Assumed false. Finishing...\n";
        let v' = neg_expr ex in
        let to_add = (match v' with | Value _ -> [] | _ -> [v']) in
        finish := true;
        Constraints.set_constraint finish_constraints !iterations (to_add @ path_cond);
        [], [], logic_env, to_add @ path_cond, sym_mem

      | SymAssume, (I32 i, ex) :: vs' ->
        let to_add = (match ex with | Value _ -> [] | _ -> [ex]) in
        Printf.printf ">>> Assume passed. Continuing execution...\n";
        vs', [], logic_env, to_add @ path_cond, sym_mem

      | SymInt32 x, vs' ->
        let v =
          try Hashtbl.find logic_env x with
          | Not_found ->
            let v' = I32 I32.random in
            Logicenv.set_sym logic_env x v';
            v'
        in (v, Symvalue.Symbolic (SymInt32, x)) :: vs', [], logic_env, path_cond, sym_mem

      | SymInt64 x, vs' ->
        let v =
          try Hashtbl.find logic_env x with 
          | Not_found ->
            let v' = I64 I64.random in
            Logicenv.set_sym logic_env x v';
            v'
        in (v, Symvalue.Symbolic (SymInt64, x)) :: vs', [], logic_env, path_cond, sym_mem

      | DynSymInt32, (I32 i, _) :: vs ->
        let x = Char.escaped (Char.chr (Int32.to_int i)) in
        (*let x = fresh_sym_var () in *)
        let v =
          try Hashtbl.find logic_env x with
          | Not_found ->
            let v' = I32 I32.random in
            Logicenv.set_sym logic_env x v';
            v'
        in (v, Symvalue.Symbolic (SymInt32, x)) :: vs, [], logic_env, path_cond, sym_mem

      | SymFloat32 x, vs' ->
        let v =
          try Hashtbl.find logic_env x with
          | Not_found ->
            let v' = F32 F32.random in
            Logicenv.set_sym logic_env x v';
            v'
        in (v, Symvalue.Symbolic (SymFloat32, x)) :: vs', [], logic_env, path_cond, sym_mem

      | SymFloat64 x, vs' ->
        let v = 
          try Hashtbl.find logic_env x with 
          | Not_found ->
            let v' = F64 F64.random in
            Logicenv.set_sym logic_env x v';
            v'
        in (v, Symvalue.Symbolic (SymFloat64, x)) :: vs', [], logic_env, path_cond, sym_mem

      | GetSymInt32 x, vs' ->
        let v =
          try Hashtbl.find logic_env x with
          | Not_found -> Crash.error e.at "Symbolic variable was not in store."
        in (v, Symvalue.Symbolic (SymInt32, x)) :: vs', [], logic_env, path_cond, sym_mem

      | GetSymInt64 x, vs' ->
        let v =
          try Hashtbl.find logic_env x with
          | Not_found -> Crash.error e.at "Symbolic variable was not in store."
        in (v, Symvalue.Symbolic (SymInt64, x)) :: vs', [], logic_env, path_cond, sym_mem

      | GetSymFloat32 x, vs' ->
        let v =
          try Hashtbl.find logic_env x with
          | Not_found -> Crash.error e.at "Symbolic variable was not in store."
        in (v, Symvalue.Symbolic (SymFloat32, x)) :: vs', [], logic_env, path_cond, sym_mem

      | GetSymFloat64 x, vs' ->
        let v =
          try Hashtbl.find logic_env x with
          | Not_found -> Crash.error e.at "Symbolic variable was not in store."
        in (v, Symvalue.Symbolic (SymFloat64, x)) :: vs', [], logic_env, path_cond, sym_mem

      | PrintStack, vs' ->
        Printf.printf "STACK STATE: %s\n" (string_of_sym_value vs');
        vs', [], logic_env, path_cond, sym_mem

      | PrintMemory, vs' ->
        Printf.printf "MEMORY STATE: \n%s"  (Symmem2.to_string sym_mem); 
        vs', [], logic_env, path_cond, sym_mem

      | PrintBtree, vs' ->
        Printf.printf "B TREE STATE: \n\n";
        Btree.print_b_tree sym_mem; 
        vs', [], logic_env, path_cond, sym_mem

      | CompareExpr, (v1, ex1) :: (v2, ex2) :: vs' ->
        let eq = Values.value_of_bool (Eval_numeric.eval_relop (Values.I32 Ast.I32Op.Eq) (I32 (Int32.of_int 1)) (I32 (Int32.of_int 1))) in
        let neq = Values.value_of_bool (Eval_numeric.eval_relop (Values.I32 Ast.I32Op.Eq) (I32 (Int32.of_int 1)) (I32 (Int32.of_int 0))) in
        let res =
          match ex1, ex2 with 
          | Symbolic (SymInt32, x), Symbolic (SymInt32, y) -> 
              if x = y then (
                eq, Symvalue.I32Relop (I32Eq, ex1, ex2)
              ) else (
                neq, Symvalue.I32Relop (I32Ne, ex1, ex2)
              )
          | _, _ -> eval_relop (v1, ex1) (v2, ex2) (Values.I32 Ast.I32Op.Eq)
        in
        res :: vs', [], logic_env, path_cond, sym_mem

      | IsSymbolic, (I32 sz, _) :: (I32 i, _) :: vs' ->
        let addr = I64_convert.extend_i32_u i in
        let (_, v) = Symmem2.load_value sym_mem addr 0l I32Type in
        let ans = begin
          match v with
          | Symbolic _ -> I32 (Int32.of_int 1)
          | _ -> I32 0l
        end
        in
        (*Printf.printf "%d %d\n" (Int32.to_int i) (Int64.to_int addr);*)
        (ans, Value ans) :: vs', [], logic_env, path_cond, sym_mem

      | _ ->
        Crash.error e.at
          ("missing or ill-typed operand on stack")
    )

    | STrapping msg, vs ->
      assert false

    | SReturning vs', vs ->
      Crash.error e.at "undefined frame"

    | SBreaking (k, vs'), vs ->
      Crash.error e.at "undefined label"

    | SLabel (n, es0, (vs', [])), vs ->
      vs' @ vs, [], logic_env, path_cond, sym_mem

    | SLabel (n, es0, (vs', {it = STrapping msg; at} :: es')), vs ->
      vs, [STrapping msg @@ at], logic_env, path_cond, sym_mem

    | SLabel (n, es0, (vs', {it = SReturning vs0; at} :: es')), vs ->
      vs, [SReturning vs0 @@ at], logic_env, path_cond, sym_mem

    | SLabel (n, es0, (vs', {it = SBreaking (0l, vs0); at} :: es')), vs ->
      take n vs0 e.at @ vs, List.map plain es0, logic_env, path_cond, sym_mem

    | SLabel (n, es0, (vs', {it = SBreaking (k, vs0); at} :: es')), vs ->
      vs, [SBreaking (Int32.sub k 1l, vs0) @@ at], logic_env, path_cond, sym_mem

    | SLabel (n, es0, code'), vs ->
      let c' = sym_step {c with sym_code = code'} in
      vs, [SLabel (n, es0, c'.sym_code) @@ e.at], c'.logic_env, c'.path_cond, c'.sym_mem

    | SFrame (n, frame', (vs', [])), vs ->
      vs' @ vs, [], logic_env, path_cond, sym_mem

    | SFrame (n, frame', (vs', {it = STrapping msg; at} :: es')), vs ->
      vs, [STrapping msg @@ at], logic_env, path_cond, sym_mem

    | SFrame (n, frame', (vs', {it = SReturning vs0; at} :: es')), vs ->
      take n vs0 e.at @ vs, [], logic_env, path_cond, sym_mem

    | SFrame (n, frame', code'), vs ->
      let c' = sym_step {sym_frame = frame'; sym_code = code'; logic_env = c.logic_env; path_cond = c.path_cond; sym_mem = c.sym_mem; sym_budget = c.sym_budget - 1} in
      vs, [SFrame (n, c'.sym_frame, c'.sym_code) @@ e.at], c'.logic_env, c'.path_cond, c'.sym_mem

    | SInvoke func, vs when c.sym_budget = 0 ->
      Exhaustion.error e.at "call stack exhausted"

    | SInvoke func, vs ->            
      let FuncType (ins, out) = Func.type_of func in
      let n = List.length ins in
      let args, vs' = take n vs e.at, drop n vs e.at in
      (match func with
      | Func.AstFunc (t, inst', f) ->
        let locals' = List.map (fun v -> v, Symvalue.Value v) (List.map default_value f.it.locals) in
        let locals'' = List.rev args @ locals' in
        let code' = [], [SPlain (Block (out, f.it.body)) @@ f.at] in
        let frame' = {sym_inst = !inst'; sym_locals = List.map ref locals''} in
        vs', [SFrame (List.length out, frame', code') @@ e.at], logic_env, path_cond, sym_mem

      | Func.HostFunc (t, f) -> failwith "HostFunc error"
        (*try List.rev (f (List.rev args)) @ vs', [], logic_env, path_cond
        with Crash (_, msg) -> Crash.error e.at msg
         *)
      )
  in {c with sym_code = vs', es' @ List.tl es; logic_env = logic_env'; path_cond = path_cond'; sym_mem = sym_mem'}


(*  Symbolic evaluation  *)
let rec sym_eval (c : sym_config) : sym_config = (* c_sym_value stack *)
  match c.sym_code with
  | vs, [] ->
    c

  | vs, {it = STrapping msg; at} :: _ ->
    Trap.error at msg

  | vs, es ->
    if !finish = true then (
      finish := false;
      c
    ) else (
      sym_eval (sym_step c)
    )

(* Functions & Constants *)
(*  Symbolic invoke  *)
let sym_invoke (func : func_inst) (vs : sym_value list) : sym_value list =
  let at = match func with Func.AstFunc (_,_, f) -> f.at | _ -> no_region in
  let inst_ref = try Option.get (Func.get_inst func) with Invalid_argument s ->
    Crash.error at ("sym_invoke: " ^ s) in
  let c = ref (sym_config empty_module_inst (List.rev vs) [SInvoke func @@ at] 
      !inst_ref.sym_memory) in
  let initial_memory = Symmem2.memcpy !inst_ref.sym_memory in
  (*  ----------------  CONCOLIC EXECUTION  ----------------  *)
  (* Model satisfiability *)
  let satisfiable = ref true in
  (* 1. Initialize the global path condition *)
  let v = Symvalue.Value (I32 0l) in
  let e = I32Relop (I32Eq, v, v) in
  let big_pi      = ref  e  in 
  let big_pi_list = ref [e] in
  let global_time_z3 = ref 0. in
  Printf.printf "\n\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n";
  (* 2. Check if the global path conditions is satisfiable *)
  while !satisfiable do
    Printf.printf "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ITERATION NUMBER %s ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n" (string_of_int !iterations);
    (* 4. Execute the concolic interpreter with the obtained model *)
    let {sym_frame = frame; 
         sym_code = vs, es; 
         logic_env; 
         path_cond = pi;
         _} = (sym_eval !c)
    in
    if pi = [] then begin 
      satisfiable := false
    end else begin
      Printf.printf "\n\n$$$$$$ LOGICAL ENVIRONMENT BEFORE Z3 STATE $$$$$$\n";
      Printf.printf "%s" (Logicenv.print_sym_store logic_env);
      Printf.printf "$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n\n";

      Printf.printf "\n\n$$$$$$ PATH CONDITIONS BEFORE Z3 $$$$$$\n";
      Printf.printf "%s\n" (pp_string_of_pc pi);
      Printf.printf "$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n";

      (* Negate the path conditions obtained in sym_eval.
        Returns sym_value that ORs all of those negations *)
      let pi_i = neg_expr (and_list pi) in
      (* ANDs pi_i with the negated expressions from previous iterations *)
      big_pi := BoolOp (And, pi_i, !big_pi);
      big_pi_list := [pi_i] @ !big_pi_list;

      Printf.printf "\n\n$$$$$$ BIG PI REPRESENTATION $$$$$$\n";
      Printf.printf "%s\n" (pp_string_of_pc [!big_pi]);
      Printf.printf "$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n\n";

      (* FOR STATISTICS: measuring the size of pi and big_pi *)
      let size_pi     = Symvalue.length (Symvalue.and_list pi) in
      let size_big_pi = Symvalue.length !big_pi in


      (* STATISTICS: measure time it takes to find a new logic environment *)
      let total_time = ref 0. in
      let start_time = Sys.time () in
      
      (* Check the satisfiability of the conditions *)     
      let model : (Z3.Model.model option) = Z3Encoding2.check_sat_core [!big_pi] in

      (* According to the satisfiability of the model... *)
      let print_str =
        match model with
        | None -> 
            satisfiable := false; 
            total_time := (Sys.time ()) -. start_time; 
            "Model is no longer satisfiable. All paths have been verified.\n"
        | Some m -> 
            (* Get variable names from the symbolic store -- according to the model *)
            let li32 = Logicenv.get_sym_int32_vars logic_env in
            let li64 = Logicenv.get_sym_int64_vars logic_env in
            let lf32 = Logicenv.get_sym_float32_vars logic_env in
            let lf64 = Logicenv.get_sym_float64_vars logic_env in

            (* Obtain new symbolic store *)
            let sym_st = Z3Encoding2.lift_z3_model m li32 li64 lf32 lf64 in
            if Logicenv.is_empty sym_st then satisfiable := false;

            total_time := (Sys.time ()) -. start_time;
            global_time_z3 := !global_time_z3 +. !total_time;
            
            let envc = Logicenv.neg_pc sym_st in
            big_pi := BoolOp (And, envc, !big_pi);
            big_pi_list := !big_pi_list @ [envc];
            !c.logic_env <- sym_st;
            !c.sym_mem   <- initial_memory;
            (*c := {!c with logic_env = sym_st; sym_mem = initial_memory};*)

            "SATISFIABLE\n" ^ 
            "MODEL: \n" ^ (Z3.Model.to_string m) ^ "\n" ^ 
            "\n\n$$$$$$ NEW LOGICAL ENVIRONMENT STATE $$$$$$\n" ^ 
            (Logicenv.print_sym_store sym_st) ^ 
            "$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n\n"
      in Printf.printf "%s" print_str;

      Printf.printf "\n------------------------ ITERATION %02d STATISTICS: ------------------------\n" !iterations;
      Printf.printf "PATH CONDITIONS SIZE: %d\n" size_pi;
      Printf.printf "GLOBAL PATH CONDITION SIZE: %d\n" size_big_pi;
      Printf.printf "TIME TO RETRIEVE NEW LOGICAL ENVIRONMENT: %f\n" !total_time;
      Printf.printf "--------------------------------------------------------------------------\n\n\n";

      Printf.printf "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n";
      iterations := !iterations + 1;
      lines := []
    end
  done;
  Printf.printf "\n\n>>>> END OF THE CONCOLIC EXECUTION. ASSUME FAILS WHEN:\n%s\n\n" (Constraints.print_constraints finish_constraints);
  Printf.printf ">>>> TEST COVERAGE LINES:\n";
  let ranges = Ranges.range_list !lines_total in
  Printf.printf "%s\n" ranges;

  Printf.printf "\n>>>> TOTAL TIME SPENT w/ THE SOLVER: %f\n" !global_time_z3;

  let (vs, _) = !c.sym_code in
  try List.rev vs with Stack_overflow ->
    Exhaustion.error at "call stack exhausted"


let eval_const (inst : module_inst) (const : const) : value =
  let sym_mem = inst.sym_memory in
  let c = sym_config inst [] (List.map plain const.it) sym_mem in
  let res = sym_eval c in
  let (vs, _) = res.sym_code in
  match vs with
  | [(v, _)] -> v
  | vs -> Crash.error const.at "wrong number of results on stack"

let i32 (v : value) at =
  match v with
  | I32 i -> i
  | _ -> Crash.error at "type error: i32 value expected"

(* Modules *)

let create_func (inst : module_inst) (f : func) : func_inst =
  Func.alloc (type_ inst f.it.ftype) (ref inst) f

let create_table (inst : module_inst) (tab : table) : table_inst =
  let {ttype} = tab.it in
  Table.alloc ttype

let create_memory (inst : module_inst) (mem : memory) : memory_inst =
  let {mtype} = mem.it in
  Memory.alloc mtype

let create_global (inst : module_inst) (glob : global) : global_inst =
  let {gtype; value} = glob.it in
  let v = eval_const inst value in
  Global.alloc gtype v

let create_export (inst : module_inst) (ex : export) : export_inst =
  let {name; edesc} = ex.it in
  let ext =
    match edesc.it with
    | FuncExport x -> ExternFunc (func inst x)
    | TableExport x -> ExternTable (table inst x)
    | MemoryExport x -> ExternMemory (memory inst x)
    | GlobalExport x -> ExternGlobal (global inst x)
  in name, ext


let init_func (inst : module_inst) (func : func_inst) =
  match func with
  | Func.AstFunc (_, inst_ref, _) -> inst_ref := inst
  | _ -> assert false

let init_table (inst : module_inst) (seg : table_segment) =
  let {index; offset = const; init} = seg.it in
  let tab = table inst index in
  let offset = i32 (eval_const inst const) const.at in
  let end_ = Int32.(add offset (of_int (List.length init))) in
  let bound = Table.size tab in
  if I32.lt_u bound end_ || I32.lt_u end_ offset then
    Link.error seg.at "elements segment does not fit table";
  fun () ->
    Table.blit tab offset (List.map (fun x -> FuncElem (func inst x)) init)

let init_memory (inst : module_inst) (seg : memory_segment) =
  let {index; offset = const; init} = seg.it in
  let mem = memory inst index in 
  let sym_mem = inst.sym_memory in
  let offset' = i32 (eval_const inst const) const.at in
  let offset = I64_convert.extend_i32_u offset' in
  let end_ = Int64.(add offset (of_int (String.length init))) in
  let bound = Memory.bound mem in
  if I64.lt_u bound end_ || I64.lt_u end_ offset then
    Link.error seg.at "data segment does not fit memory";
  fun () -> (Symmem2.store_bytes sym_mem offset init)
  (*fun () -> (Memory.store_bytes mem offset init; 
             Symmem.store_bytes sym_mem offset init)*)

let add_import (m : module_) (ext : extern) (im : import) (inst : module_inst)
  : module_inst =
  if not (match_extern_type (extern_type_of ext) (import_type m im)) then
    Link.error im.at "incompatible import type";
  match ext with
  | ExternFunc func -> {inst with funcs = func :: inst.funcs}
  | ExternTable tab -> {inst with tables = tab :: inst.tables}
  | ExternMemory mem -> {inst with memories = mem :: inst.memories}
  | ExternGlobal glob -> {inst with globals = glob :: inst.globals}

let init (m : module_) (exts : extern list) : module_inst =
  let
    { imports; tables; memories; globals; funcs; types;
      exports; elems; data; start
    } = m.it
  in
  if List.length exts <> List.length imports then
    Link.error m.at "wrong number of imports provided for initialisation";
  let inst0 =
    { (List.fold_right2 (add_import m) exts imports empty_module_inst) with
      types = List.map (fun type_ -> type_.it) types }
  in
  let fs = List.map (create_func inst0) funcs in
  let inst1 =
    { inst0 with
      funcs = inst0.funcs @ fs;
      tables = inst0.tables @ List.map (create_table inst0) tables;
      memories = inst0.memories @ List.map (create_memory inst0) memories;
      globals = inst0.globals @ List.map (create_global inst0) globals;
    }
  in
  let inst = {inst1 with exports = List.map (create_export inst1) exports} in
  List.iter (init_func inst) fs;
  let init_elems = List.map (init_table inst) elems in
  let init_datas = List.map (init_memory inst) data in
  List.iter (fun f -> f ()) init_elems;
  List.iter (fun f -> f ()) init_datas;
  Lib.Option.app (fun x -> ignore (sym_invoke (func inst x) [])) start;
  inst
