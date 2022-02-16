
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
  | Symmem2.InvalidAddress a ->
      (Int64.to_string a) ^ ":address not found in hashtable"
  | Symmem2.Bounds -> "out of bounds memory access"
  (* TODO: might just remove these *)
  | Memory.SizeOverflow -> "memory size overflow"
  | Memory.SizeLimit -> "memory size limit reached"
  | Memory.Type -> Crash.error at "type mismatch at memory access"
  | exn -> raise exn

let numeric_error at = function
  | Evaluations.UnsupportedOp m ->  m ^ ": unsupported operation"
  | Numeric_error.IntegerOverflow -> "integer overflow"
  | Numeric_error.IntegerDivideByZero -> "integer divide by zero"
  | Numeric_error.InvalidConversionToInteger -> "invalid conversion to integer"
  | Eval_numeric.TypeError (i, v, t) ->
    Crash.error at
      ("type error, expected " ^ Types.string_of_value_type t ^ " as operand " ^
       string_of_int i ^ ", got " ^ Types.string_of_value_type (Values.type_of v))
  | exn -> raise exn

type bug =
  | Overflow
  | UAF
  | InvalidFree

type interruption =
  | IntLimit
  | AsmFail of path_conditions
  | AssFail of string
  | Bug of bug * string

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
  (**
    * Wasp's administrative instructions to halt
    * small-step semantic intepretation
    *)
  | Interrupt of interruption

(* Symbolic configuration  *)
type sym_config =
{
  sym_frame  : sym_frame;
  sym_code   : sym_code;
  logic_env  : Logicenv.t;
  path_cond  : path_conditions;
  sym_mem    : Symmem2.t;
  sym_budget : int;  (* to model stack overflow *)
}

(* Symbolic frame and configuration  *)
let sym_frame sym_inst sym_locals = {sym_inst; sym_locals}
let sym_config inst vs es sym_m = {
  sym_frame  = sym_frame inst [];
  sym_code   = vs, es;
  logic_env  = Logicenv.create [];
  path_cond  = [];
  sym_mem    = sym_m;
  sym_budget = 100000 (* models default recursion limit in a system *)
}

exception InstrLimit of sym_config
exception AssumeFail of sym_config * path_conditions
exception AssertFail of sym_config * region * string
exception BugException of bug * region * string
exception Unsatisfiable

let lines_to_ignore = ref 0

let assumes     = ref []

let instr_cnt   = ref 0

let iterations  = ref 1

let incomplete  = ref false

(* Time statistics *)
let solver_time = ref 0.

let chunk_table = Hashtbl.create 512

(* Helpers *)
let debug str = if !Flags.trace then print_endline str
let time_call f args acc =
  let start = Sys.time () in
  let ret = f args in
  acc := !acc +. ((Sys.time ()) -. start);
  ret

let string_of_bug : (bug -> string) = function
  | Overflow -> "Overflow"
  | UAF      -> "Use After Free"
  | InvalidFree -> "Invalid Free"

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
  instr_cnt := !instr_cnt + 1;
  let {sym_frame = frame; sym_code = vs, es; logic_env; path_cond = pc; sym_mem = mem; _} = c in
  let e = List.hd es in
  Coverage.record_line (Source.get_line e.at);
  let vs', es', logic_env', pc', mem' =
    if (!Flags.instr_max != -1) && (!instr_cnt >= !Flags.instr_max) then (
      incomplete := true;
      vs, [(Interrupt (IntLimit)) @@ e.at], logic_env, pc, mem
    ) else (match e.it, vs with
    | SPlain e', vs ->
      (*Printf.printf ("\n Instr: %s\nStack:\n %s\n##################################################\n\n") (instr_str e') (Symvalue.print_c_sym_values vs);*)
      (match e', vs with
      | Unreachable, vs ->
        vs, [STrapping "unreachable executed" @@ e.at], logic_env, pc, mem

      | Nop, vs ->
        vs, [], logic_env, pc, mem

      | Block (ts, es'), vs ->
        vs, [SLabel (List.length ts, [], ([], List.map plain es')) @@ e.at], logic_env, pc, mem

      | Loop (ts, es'), vs ->
        vs, [SLabel (0, [e' @@ e.at], ([], List.map plain es')) @@ e.at], logic_env, pc, mem

      | If (ts, es1, es2), (I32 0l, ex) :: vs' ->
        let pc = add_constraint ex pc true in
        (*Printf.printf ("\n\n###### Entered IF, with 0 on top of stack. ######\nPath conditions are now:\n %s\n#################################################\n\n")   (Symvalue.str_pc ([v'] @ pc));*)
        vs', [SPlain (Block (ts, es2)) @@ e.at], logic_env, pc, mem

      | If (ts, es1, es2), (I32 i, ex) :: vs' ->
        let pc = add_constraint ex pc false in
        (*Printf.printf ("\n\n###### Entered IF, with !=0 on top of stack. ######\nPath conditions are now:\n %s\n##################################################\n\n")   (Symvalue.str_pc ([v'] @ pc));*)
        vs', [SPlain (Block (ts, es1)) @@ e.at], logic_env, pc, mem

      | Br x, vs ->
        [], [SBreaking (x.it, vs) @@ e.at], logic_env, pc, mem

      | BrIf x, (I32 0l, ex) :: vs' ->
        (* Negate expression because it is false *)
        let pc = add_constraint ex pc true in
        (*Printf.printf ("\n\n###### Entered BRIF, with 0 on top of stack @ (%s) ######\nPath conditions are now:\n %s\n#################################################\n\n") (Source.string_of_region e.at) (Symvalue.pp_string_of_pc
         (to_add @ pc));*)
        vs', [], logic_env, pc, mem

      | BrIf x, (I32 i, ex) :: vs' ->
        let pc = add_constraint ex pc false in
        (*Printf.printf ("\n\n###### Entered IF, with !=0 on top of stack @ (%s) ######\nPath conditions are now:\n %s\n##################################################\n\n") (Source.string_of_region e.at) (Symvalue.pp_string_of_pc (to_add @ pc));*)
        vs', [SPlain (Br x) @@ e.at], logic_env, pc, mem

      | BrTable (xs, x), (I32 i, _) :: vs' when I32.ge_u i (Lib.List32.length xs) ->
        vs', [SPlain (Br x) @@ e.at], logic_env, pc, mem

      | BrTable (xs, x), (I32 i, _) :: vs' ->
        vs', [SPlain (Br (Lib.List32.nth xs i)) @@ e.at], logic_env, pc, mem

      | Return, vs ->
        [], [SReturning vs @@ e.at], logic_env, pc, mem

      | Call x, vs ->
        vs, [SInvoke (func frame.sym_inst x) @@ e.at], logic_env, pc, mem

      | CallIndirect x, (I32 i, _) :: vs ->
        let func = func_elem frame.sym_inst (0l @@ e.at) i e.at in
        if type_ frame.sym_inst x <> Func.type_of func then
          vs, [STrapping "indirect call type mismatch" @@ e.at], logic_env, pc, mem
        else
          vs, [SInvoke func @@ e.at], logic_env, pc, mem

      | Drop, v :: vs' ->
        vs', [], logic_env, pc, mem

      | Select, (I32 0l, ex) :: v2 :: v1 :: vs' ->
        let pc = add_constraint ex pc true in
        v2 :: vs', [], logic_env, pc, mem

      | Select, (I32 i, ex) :: v2 :: v1 :: vs' ->
        let pc = add_constraint ex pc false in
        v1 :: vs', [], logic_env, pc , mem

      | LocalGet x, vs ->
        !(local frame x) :: vs, [], logic_env, pc, mem

      | LocalSet x, v :: vs' ->
        local frame x := v;
        vs', [], logic_env, pc, mem

      | LocalTee x, v :: vs' ->
        local frame x := v;
        v :: vs', [], logic_env, pc, mem

      | GlobalGet x, vs ->
        let v' = Global.load (global frame.sym_inst x) in
        (v', Value v') :: vs, [], logic_env, pc, mem

      | GlobalSet x, (v, _) :: vs' ->
        (try
          Global.store (global frame.sym_inst x) v; vs', [], logic_env, pc, mem
        with  Global.NotMutable -> Crash.error e.at "write to immutable global"
            | Global.Type -> Crash.error e.at "type mismatch at global write")

      | Load {offset; ty; sz; _}, (I32 i, sym_ptr) :: vs' ->
        let base = I64_convert.extend_i32_u i in
        (* overflow check *)
        let ptr = get_ptr (simplify sym_ptr) in
        begin try
          if Option.is_some ptr then begin
            let low = I32Value.of_value (Option.get ptr) in
            let chunk_size = try Hashtbl.find chunk_table low with
                             | Not_found -> raise (BugException (UAF, e.at, "")) in
            let high = Int64.(add (of_int32 low) (of_int32 chunk_size))
            and ptr_val = Int64.(add base (of_int32 offset)) in
            (* ptr_val \notin [low, high[ => overflow *)
            if ptr_val < (Int64.of_int32 low) || ptr_val >= high then
              raise (BugException (Overflow, e.at, ""))
          end;
          let (v, e) =
            match sz with
            | None           -> Symmem2.load_value mem base offset ty
            | Some (sz, ext) -> Symmem2.load_packed sz ext mem base offset ty
          in (v, e) :: vs', [], logic_env, pc, mem
        with
        | BugException (b, at, _) ->
          vs', [(Interrupt (Bug (b, Logicenv.(to_json (to_list logic_env))))) @@ e.at], logic_env, pc, mem
        | exn ->
          vs', [STrapping (memory_error e.at exn) @@ e.at], logic_env, pc, mem
        end

      | Store {offset; sz; _}, (v, ex) :: (I32 i, sym_ptr) :: vs' ->
        let base = I64_convert.extend_i32_u i in
        let ptr = get_ptr (simplify sym_ptr) in
        begin try
          if Option.is_some ptr then begin
            let low = I32Value.of_value (Option.get ptr) in
            let chunk_size = try Hashtbl.find chunk_table low with
                             | Not_found -> raise (BugException (UAF, e.at, "")) in
            let high = Int64.(add (of_int32 low) (of_int32 chunk_size))
            and ptr_val = Int64.(add base (of_int32 offset)) in
            if (Int64.of_int32 low) > ptr_val || ptr_val >= high then
              raise (BugException (Overflow, e.at, ""))
          end;
          begin match sz with
          | None    -> Symmem2.store_value mem base offset (v, ex)
          | Some sz -> Symmem2.store_packed sz mem base offset (v, ex)
          end;
          vs', [], logic_env, pc, mem
        with
        | BugException (b, at, _) ->
          vs', [(Interrupt (Bug (b, Logicenv.(to_json (to_list logic_env))))) @@ e.at], logic_env, pc, mem
        | exn ->
          vs', [STrapping (memory_error e.at exn) @@ e.at], logic_env, pc, mem
        end

      | MemorySize, vs ->
        let mem' = memory frame.sym_inst (0l @@ e.at) in
        (I32 (Memory.size mem'), Value (I32 (Memory.size mem'))) :: vs, [], logic_env, pc, mem

      | MemoryGrow, (I32 delta, _) :: vs' ->
        let mem' = memory frame.sym_inst (0l @@ e.at) in
        let old_size = Memory.size mem' in
        let result =
          try Memory.grow mem' delta; old_size
          with Memory.SizeOverflow | Memory.SizeLimit | Memory.OutOfMemory -> -1l
        in (I32 result, Value (I32 result)) :: vs', [], logic_env, pc, mem

      | Const v, vs ->
        (v.it, Value (v.it)) :: vs, [], logic_env, pc, mem

      | Test testop, v :: vs' ->
        (try
          let new_conf = eval_testop v testop in
          new_conf :: vs', [], logic_env, pc, mem
        with exn -> vs', [STrapping (numeric_error e.at exn) @@ e.at], logic_env, pc, mem)

      | Compare relop, v2 :: v1 :: vs' ->
        (try
          let new_conf = eval_relop v1 v2 relop in
          new_conf :: vs', [], logic_env, pc, mem
        with exn -> vs', [STrapping (numeric_error e.at exn) @@ e.at], logic_env, pc, mem)

      | Unary unop, v :: vs' ->
        (try
          let new_conf = eval_unop v unop in
          new_conf :: vs', [], logic_env, pc, mem
        with exn -> vs', [STrapping (numeric_error e.at exn) @@ e.at], logic_env, pc, mem)

      | Binary binop, v2 :: v1 :: vs' ->
        (try
          let new_conf = eval_binop v1 v2 binop in
          new_conf :: vs', [], logic_env, pc, mem
        with exn -> vs', [STrapping (numeric_error e.at exn) @@ e.at], logic_env, pc, mem)

      | Convert cvtop, v :: vs' ->
        (try
          let v' = eval_cvtop cvtop v in
          v' :: vs', [], logic_env, pc, mem
        with exn -> vs', [STrapping (numeric_error e.at exn) @@ e.at], logic_env, pc, mem)

      | Dup, v :: vs' ->
        v :: v :: vs', [], logic_env, pc, mem

      | SymAssert, (I32 0l, ex) :: vs' -> (* 0 on top of stack *)
        debug ">>> Assert FAILED! Stopping...";
        let es' =
          [Interrupt (AssFail Logicenv.(to_json (to_list logic_env))) @@ e.at]
        in vs', es', logic_env, pc, mem

      | SymAssert, (I32 i, ex) :: vs' -> (* != 0 on top of stack *)
        debug ">>> Assert reached. Checking satisfiability...";
        let es' =
          if pc = [] && !assumes = [] then []
          else
            match simplify ex with
            | Value (I32 v) when not (v = 0l) -> []
            | Ptr   (I32 v) when not (v = 0l) -> []
            | ex' ->
              let c = Option.map negate_relop (to_constraint ex') in
              let pc' = Option.map_default (fun a -> a :: pc) pc c in
              let assertion = Formula.to_formula (!assumes @ pc') in
              let start = Sys.time () in
              let model = Z3Encoding2.check_sat_core assertion in
              solver_time := !solver_time +. ((Sys.time ()) -. start);
              match model with
              | None   -> []
              | Some m ->
                let li32 = Logicenv.get_vars_by_type I32Type logic_env
                and li64 = Logicenv.get_vars_by_type I64Type logic_env
                and lf32 = Logicenv.get_vars_by_type F32Type logic_env
                and lf64 = Logicenv.get_vars_by_type F64Type logic_env in
                let binds = Z3Encoding2.lift_z3_model m li32 li64 lf32 lf64 in
                Logicenv.update logic_env binds;
                [Interrupt (AssFail Logicenv.(to_json (to_list logic_env))) @@ e.at]
        in
        if es' = [] then
          debug "\n\n###### Assertion passed ######";
        vs', es', logic_env, pc, mem

      | SymAssume, (I32 0l, ex) :: vs' ->
        debug (">>> Assumed false {line> " ^ (Source.string_of_pos e.at.left) ^
          "}. Finishing...");
        let cond = to_constraint (simplify ex) in
        assumes := Option.map_default (fun a -> a :: !assumes) !assumes cond;
        if (!assumes = []) || (not (pc = [])) then
          vs', [Interrupt (AsmFail !assumes) @@ e.at], logic_env, pc, mem
        else (
          let assertion = Formula.to_formula (!assumes @ pc) in
          let model = time_call Z3Encoding2.check_sat_core assertion solver_time in
          let vs'', es' = match model with
            | None -> vs', [Interrupt (AsmFail !assumes) @@ e.at]
            | Some m ->
              let li32 = Logicenv.get_vars_by_type I32Type logic_env
              and li64 = Logicenv.get_vars_by_type I64Type logic_env
              and lf32 = Logicenv.get_vars_by_type F32Type logic_env
              and lf64 = Logicenv.get_vars_by_type F64Type logic_env in
              let binds = Z3Encoding2.lift_z3_model m li32 li64 lf32 lf64 in
              (* update logical environment *)
              Logicenv.update logic_env binds;
              (* update heap *)
              Symmem2.update mem logic_env;
              let f = (fun v -> let (_, s) = v in (Logicenv.eval logic_env s, s)) in
              (* update locals *)
              List.iter (fun a -> a := f !a) frame.sym_locals;
              (* update stack *)
              List.map f vs', []
          in vs'', es', logic_env, pc, mem)

      | SymAssume, (I32 i, ex) :: vs' ->
        let cond = to_constraint (simplify ex) in
        assumes := Option.map_default (fun a -> a :: !assumes) !assumes cond;
        (* let pc' = Option.map_default (fun a -> a :: pc) pc cond in *)
        debug ">>> Assume passed. Continuing execution...";
        vs', [], logic_env, pc, mem

      | Symbolic (ty, b), (I32 i, _) :: vs' ->
        let base = I64_convert.extend_i32_u i in
        let x = Logicenv.next logic_env (Symmem2.load_string mem base) in
        let v = Logicenv.get logic_env x ty b in
        (v, to_symbolic ty x) :: vs', [], logic_env, pc, mem

      | Boolop boolop, (v2, sv2) :: (v1, sv1) :: vs' ->
        let sv2' = mk_relop sv2 (Values.type_of v2) in
        let v2' = Values.(value_of_bool (not (v2 = default_value (type_of v2)))) in
        let sv1' = mk_relop sv1 (Values.type_of v1) in
        let v1' = Values.(value_of_bool (not (v1 = default_value (type_of v1)))) in
        (try
          let v3, sv3 = eval_binop (v1', sv1') (v2', sv2') boolop in
          (v3, simplify sv3) :: vs', [], logic_env, pc, mem
        with exn ->
          vs', [STrapping (numeric_error e.at exn) @@ e.at], logic_env, pc, mem)

      | Alloc, (I32 a, sa) :: (I32 b, sb) :: vs' ->
          Hashtbl.add chunk_table b a;
          (I32 b, Ptr (I32 b)) :: vs', [], logic_env, pc, mem

      | Free, (I32 i, _) :: vs' ->
        let es' =
          if not (Hashtbl.mem chunk_table i) then [Interrupt (Bug (InvalidFree,Logicenv.(to_json (to_list logic_env)))) @@ e.at]
                                             else (Hashtbl.remove chunk_table i; [])
        in vs', es', logic_env, pc, mem

      | SymInt32 x, vs' ->
        let v =
          try Logicenv.find logic_env x with
          | Not_found ->
            let v' = I32 (I32.rand 1000) in
            Logicenv.add logic_env x v';
            v'
        in (v, Symvalue.Symbolic (SymInt32, x)) :: vs', [], logic_env, pc, mem

      | SymInt64 x, vs' ->
        let v =
          try Logicenv.find logic_env x with
          | Not_found ->
            let v' = I64 (I64.rand 1000) in
            Logicenv.add logic_env x v';
            v'
        in (v, Symvalue.Symbolic (SymInt64, x)) :: vs', [], logic_env, pc, mem

      | SymFloat32 x, vs' ->
        let v =
          try Logicenv.find logic_env x with
          | Not_found ->
            let v' = F32 (F32.rand 1000.0) in
            Logicenv.add logic_env x v';
            v'
        in (v, Symvalue.Symbolic (SymFloat32, x)) :: vs', [], logic_env, pc, mem

      | SymFloat64 x, vs' ->
        let v =
          try Logicenv.find logic_env x with
          | Not_found ->
            let v' = F64 (F64.rand 1000.0) in
            Logicenv.add logic_env x v';
            v'
        in (v, Symvalue.Symbolic (SymFloat64, x)) :: vs', [], logic_env, pc, mem

      | GetSymInt32 x, vs' ->
        let v =
          try Logicenv.find logic_env x with
          | Not_found -> Crash.error e.at "Symbolic variable was not in store."
        in (v, Symvalue.Symbolic (SymInt32, x)) :: vs', [], logic_env, pc, mem

      | GetSymInt64 x, vs' ->
        let v =
          try Logicenv.find logic_env x with
          | Not_found -> Crash.error e.at "Symbolic variable was not in store."
        in (v, Symvalue.Symbolic (SymInt64, x)) :: vs', [], logic_env, pc, mem

      | GetSymFloat32 x, vs' ->
        let v =
          try Logicenv.find logic_env x with
          | Not_found -> Crash.error e.at "Symbolic variable was not in store."
        in (v, Symvalue.Symbolic (SymFloat32, x)) :: vs', [], logic_env, pc, mem

      | GetSymFloat64 x, vs' ->
        let v =
          try Logicenv.find logic_env x with
          | Not_found -> Crash.error e.at "Symbolic variable was not in store."
        in (v, Symvalue.Symbolic (SymFloat64, x)) :: vs', [], logic_env, pc, mem

      | TernaryOp, (I32 r0c, r0s) :: (I32 r1c, r1s) :: (I32 c, s) :: vs' ->
        let x = "ternary_" ^ (string_of_int e.at.left.line) in
        let cv = I32 (if c = 0l then r0c else r1c) in
        let branch = to_constraint (simplify s) in
        let var = to_symbolic (Values.type_of cv) x in
        let v =
          if Option.is_none branch then (cv, if c = 0l then r0s else r1s)
          else (
            let branch = Option.get branch in
            let eq'  = I32Relop (Si32.I32Eq, var, r1s) in
            let imp' = I32Binop (Si32.I32Or, negate_relop branch, eq') in
            let eq   = I32Relop (Si32.I32Eq, var, r0s) in
            let imp  = I32Binop (Si32.I32Or, branch, eq) in
            let cond = I32Relop (Si32.I32Eq,
              I32Binop (Si32.I32And, imp', imp), Value (I32 1l)) in
            assumes := cond :: !assumes;
            Logicenv.add logic_env x cv;
            (cv, var)
          )
        in v :: vs', [], logic_env, pc, mem

      | TraceCondition, (I32 id, _) :: (ci, si) :: vs' ->
        (*
        let cond_str =
          (string_of_int (if ci = Values.(default_value (type_of ci)) then 0 else 1)) in
        prefix := [cond_str] @ !prefix;
        let id_s = (Int32.to_string id)
        and ci_s = (string_of_int
        and si_s = Symvalue.to_string si in
        let lbl  = !prefix ^ id_s ^ ci_s in prefix := lbl;
        let hist = try History.find history lbl with Not_found -> "" in
        let value = match hist with
          | "" -> History.add history lbl (Symvalue.to_string si);
            true
          | s when s = si_s       -> false
          | s when not (s = si_s) -> false
          | _ -> failwith "UnrecoverableError"
        in
        skip := value;
        *)
        (ci, si) :: vs', [], logic_env, pc, mem

      | PrintStack, vs' ->
        debug ("STACK STATE: " ^ (string_of_sym_value vs'));
        vs', [], logic_env, pc, mem

      | PrintMemory, vs' ->
        debug ("MEMORY STATE:\n" ^ (Symmem2.to_string mem));
        vs', [], logic_env, pc, mem

      | PrintBtree, vs' ->
        Printf.printf "B TREE STATE: \n\n";
        Btree.print_b_tree mem;
        vs', [], logic_env, pc, mem

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
        res :: vs', [], logic_env, pc, mem

      | IsSymbolic, (I32 n, _) :: (I32 i, _) :: vs' ->
        let base = I64_convert.extend_i32_u i in
        let (_, v) = Symmem2.load_bytes mem base (Int32.to_int n) in
        (* TODO: Better symbolic matcher (deal with extract of symbolics) *)
        let ans =
          begin match v with
          | Symbolic _ -> I32 1l
          | _ -> I32 0l
          end
        in
        (*Printf.printf "%d %d\n" (Int32.to_int i) (Int64.to_int addr);*)
        (ans, Value ans) :: vs', [], logic_env, pc, mem

      | _ ->
        Crash.error e.at
          ("missing or ill-typed operand on stack")
    )

    | STrapping msg, vs ->
      assert false

    | Interrupt i, vs ->
      assert false

    | SReturning vs', vs ->
      Crash.error e.at "undefined frame"

    | SBreaking (k, vs'), vs ->
      Crash.error e.at "undefined label"

    | SLabel (n, es0, (vs', [])), vs ->
      vs' @ vs, [], logic_env, pc, mem

    | SLabel (n, es0, (vs', {it = Interrupt i; at} :: es')), vs ->
      vs, [Interrupt i @@ at] @ [SLabel (n, es0, (vs', es')) @@ e.at], logic_env, pc, mem

    | SLabel (n, es0, (vs', {it = STrapping msg; at} :: es')), vs ->
      vs, [STrapping msg @@ at], logic_env, pc, mem

    | SLabel (n, es0, (vs', {it = SReturning vs0; at} :: es')), vs ->
      vs, [SReturning vs0 @@ at], logic_env, pc, mem

    | SLabel (n, es0, (vs', {it = SBreaking (0l, vs0); at} :: es')), vs ->
      take n vs0 e.at @ vs, List.map plain es0, logic_env, pc, mem

    | SLabel (n, es0, (vs', {it = SBreaking (k, vs0); at} :: es')), vs ->
      vs, [SBreaking (Int32.sub k 1l, vs0) @@ at], logic_env, pc, mem

    | SLabel (n, es0, code'), vs ->
      let c' = sym_step {c with sym_code = code'} in
      vs, [SLabel (n, es0, c'.sym_code) @@ e.at], c'.logic_env, c'.path_cond, c'.sym_mem

    | SFrame (n, frame', (vs', [])), vs ->
      vs' @ vs, [], logic_env, pc, mem

    | SFrame (n, frame', (vs', {it = Interrupt i; at} :: es')), vs ->
      vs, [Interrupt i @@ at] @ [SFrame (n, frame', (vs', es')) @@ e.at], logic_env, pc, mem

    | SFrame (n, frame', (vs', {it = STrapping msg; at} :: es')), vs ->
      vs, [STrapping msg @@ at], logic_env, pc, mem

    | SFrame (n, frame', (vs', {it = SReturning vs0; at} :: es')), vs ->
      take n vs0 e.at @ vs, [], logic_env, pc, mem

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
        vs', [SFrame (List.length out, frame', code') @@ e.at], logic_env, pc, mem

      | Func.HostFunc (t, f) -> failwith "HostFunc error"
        (*try List.rev (f (List.rev args)) @ vs', [], logic_env, pc
        with Crash (_, msg) -> Crash.error e.at msg
         *)
      )
    )
  in {c with sym_code = vs', es' @ List.tl es; logic_env = logic_env'; path_cond = pc'; sym_mem = mem'}


(*  Symbolic evaluation  *)
let rec sym_eval (c : sym_config) : sym_config = (* c_sym_value stack *)
  match c.sym_code with
  | vs, [] ->
    c

  | vs, {it = STrapping msg; at} :: _ ->
    Trap.error at msg

  | vs, {it = Interrupt i; at} :: es ->
      let exn = match i with
        | IntLimit    -> InstrLimit c
        | AsmFail pc  -> AssumeFail ({c with sym_code = vs, es}, pc)
        | AssFail wit -> AssertFail (c, at, wit)
        | Bug (b, wit)-> BugException (b, at, wit)
      in raise exn

  | vs, es ->
    sym_eval (sym_step c)

(* Functions & Constants *)
module Globalpc = Map.Make(String)

let counter = ref 0
let next_int () =
  fun () ->
    counter := !counter + 1;
    !counter

let write_test_case out_dir fmt test_data : unit =
  let i = next_int () in
  Io.save_file (Printf.sprintf fmt out_dir (i ())) test_data

let sym_invoke' (func : func_inst) (vs : sym_value list) : sym_value list =
  Sys.(set_signal sigalrm (Signal_handle (fun i -> instr_cnt := !Flags.instr_max)));
  ignore (Unix.alarm 895);
  let at = match func with Func.AstFunc (_, _, f) -> f.at | _ -> no_region in
  let inst = try Option.get (Func.get_inst func) with Invalid_argument s ->
    Crash.error at ("sym_invoke: " ^ s) in
  let c = ref (sym_config empty_module_inst (List.rev vs) [SInvoke func @@ at]
    !inst.sym_memory) in
  (* Prepare output *)
  let test_suite = Filename.concat !Flags.output "test_suite" in
  Io.safe_mkdir test_suite;
  (* Initial memory config *)
  let initial_memory = Symmem2.to_list !inst.sym_memory in
  let initial_globals = Global.contents !inst.globals in
  (* Assume constraints are stored here *)
  let finish_constraints = Constraints.create in
  let initial_sym_code = !c.sym_code in
  (* Concolic execution *)
  let rec loop global_pc =
    debug ((String.make 35 '~') ^ " ITERATION NUMBER " ^
        (string_of_int !iterations) ^ " " ^ (String.make 35 '~') ^ "\n");
    let {logic_env; path_cond = pc; sym_frame; sym_code; _} = try sym_eval !c with
      | InstrLimit conf ->
          let {logic_env; _} = conf in
          write_test_case test_suite "%s/test_%05d.json" Logicenv.(to_json (to_list logic_env));
          raise Unsatisfiable
      | AssumeFail (conf, cons) ->
          Constraints.add finish_constraints !iterations cons;
          conf
      | AssertFail (conf, at, wit) ->
          debug ("\n" ^ (string_of_region at) ^ ": Assertion Failure\n" ^ wit);
          if not !Flags.branches then raise (AssertFail (conf, at, wit))
                  else conf
      | Trap (at, msg) -> Trap.error at msg
      | e -> raise e
    in
    if (pc = []) && (!assumes = []) then
      raise Unsatisfiable;

    (* write current model as a test *)
    write_test_case test_suite "%s/test_%05d.json" Logicenv.(to_json (to_list logic_env));

   (* DEBUG: *)
    let delim = String.make 6 '$' in
    debug ("\n\n" ^ delim ^ " LOGICAL ENVIRONMENT BEFORE Z3 STATE " ^ delim ^
           "\n" ^ (Logicenv.to_string logic_env) ^ (String.make 48 '$') ^ "\n");
    debug ("\n\n" ^ delim ^ " PATH CONDITIONS BEFORE Z3 " ^ delim ^
           "\n" ^ (pp_string_of_pc pc) ^ "\n" ^ (String.make 38 '$'));

    let pc' = if not (pc = []) then Formula.(negate (to_formula pc))
                               else Formula.True in
    let global_pc' = Globalpc.add (Formula.to_string pc') pc' global_pc in
    let assumes' = List.map (fun e -> Formula.Relop e) !assumes in
    let global_pc' = List.fold_left
      (fun a b -> Globalpc.add (Formula.to_string b) b a) global_pc' assumes' in

    let bindings = List.map (fun (_, f) -> f) (Globalpc.bindings global_pc') in
    let formula = (Formula.conjuct bindings) in

    debug ("\n\n" ^ delim ^ " GLOBAL PATH CONDITION " ^ delim ^ "\n" ^
           (Formula.pp_to_string formula) ^ "\n" ^ (String.make 28 '$') ^ "\n");

    let start = Sys.time () in
    let opt_model = Z3Encoding2.check_sat_core formula in
    let curr_time = (Sys.time ()) -. start in
    solver_time := !solver_time +. curr_time;


    let model = try Option.get opt_model with _ ->
      raise Unsatisfiable in

    let li32 = Logicenv.get_vars_by_type I32Type logic_env in
    let li64 = Logicenv.get_vars_by_type I64Type logic_env in
    let lf32 = Logicenv.get_vars_by_type F32Type logic_env in
    let lf64 = Logicenv.get_vars_by_type F64Type logic_env in
    (* 3. Obtain a concrete model for the global path condition *)
    let binds = Z3Encoding2.lift_z3_model model li32 li64 lf32 lf64 in

    if binds = [] then
      raise Unsatisfiable;

    (* Prepare next iteration *)
    assumes := [];
    Hashtbl.reset chunk_table;
    Logicenv.reset logic_env;
    Logicenv.init logic_env binds;
    Symmem2.clear !c.sym_mem;
    Symmem2.init !c.sym_mem initial_memory;
    Instance.set_globals !inst initial_globals;
    c := {!c with sym_budget = 100000; sym_code = initial_sym_code; path_cond = []};

    let formula_len = Formula.length formula in
    let z3_model_str = Z3.Model.to_string model in
    debug ("SATISFIABLE\nMODEL: \n" ^ z3_model_str ^ "\n\n\n" ^
           delim ^ " NEW LOGICAL ENV STATE " ^ delim ^ "\n" ^
           (Logicenv.to_string logic_env) ^ (String.make 28 '$') ^ "\n");
    debug ("\n" ^ (String.make 23 '-') ^ " ITERATION " ^
           (string_of_int !iterations) ^ " STATISTICS: " ^ (String.make 23 '-'));
    debug ("PATH CONDITION SIZE: " ^ (string_of_int (Formula.length pc')));
    debug ("GLOBAL PATH CONDITION SIZE: " ^ (string_of_int formula_len));
    debug ("TIME TO SOLVE GLOBAL PC: " ^ (string_of_float curr_time) ^ "\n" ^
           (String.make 73 '-') ^ "\n\n");
    debug ((String.make 92 '~') ^ "\n");

    iterations := !iterations + 1;
    (*let env_constraint = Formula.to_formula (Logicenv.to_expr logic_env) in*)
    loop global_pc'
  in

  debug ((String.make 92 '~') ^ "\n");
  let global_pc = Globalpc.add "True" Formula.True Globalpc.empty in
  let loop_start = Sys.time () in
  let spec, reason, wit = try loop global_pc with
    | Unsatisfiable ->
        debug "Model is no longer satisfiable. All paths have been verified.\n";
        true, "{}", "[]"
    | AssertFail (_, r, wit) ->
        incomplete := true;
        let reason = "{" ^
          "\"type\" : \""    ^ "Assertion Failure" ^ "\", " ^
          "\"line\" : \"" ^ (Source.string_of_pos r.left ^
              (if r.right = r.left then "" else "-" ^ string_of_pos r.right)) ^ "\"" ^
        "}"
        in
        write_test_case test_suite "%s/witness_%05d.json" wit;
        false, reason, wit
    | BugException (b, r, wit) ->
        incomplete := true;
        let reason = "{" ^
          "\"type\" : \""    ^ (string_of_bug b) ^ "\", " ^
          "\"line\" : \"" ^ (Source.string_of_pos r.left ^
              (if r.right = r.left then "" else "-" ^ string_of_pos r.right)) ^ "\"" ^
        "}"
        in
        write_test_case test_suite "%s/witness_%05d.json" wit;
        false, reason, wit
    | e -> raise e
  in
  let loop_time = (Sys.time ()) -. loop_start in
  (* DEBUG: *)
  debug ("\n\n>>>> END OF CONCOLIC EXECUTION. ASSUME FAILS WHEN:\n" ^
      (Constraints.to_string finish_constraints) ^ "\n");

  let n_lines = List.((length !inst.types) + (length !inst.tables) +
                      (length !inst.memories) + (length !inst.globals) +
                      (length !inst.exports) + 1) in
  let coverage = (Coverage.calculate_cov inst (n_lines + !lines_to_ignore)) *. 100.0 in

  (* Execution report *)
  let fmt_str = "{" ^
    "\"specification\": "        ^ (string_of_bool spec)          ^ ", " ^
    "\"reason\" : "              ^ reason                         ^ ", " ^
    "\"witness\" : "             ^ wit                            ^ ", " ^
    "\"coverage\" : \""          ^ (string_of_float coverage)     ^ "\", " ^
    "\"loop_time\" : \""         ^ (string_of_float loop_time)    ^ "\", " ^
    "\"solver_time\" : \""       ^ (string_of_float !solver_time) ^ "\", " ^
    "\"paths_explored\" : "      ^ (string_of_int !iterations)    ^ ", " ^
    "\"instruction_counter\" : " ^ (string_of_int !instr_cnt)     ^ ", " ^
    "\"incomplete\" : "          ^ (string_of_bool !incomplete)   ^
  "}"
  in Io.save_file (Filename.concat !Flags.output "report.json") fmt_str;

  let (vs, _) = !c.sym_code in
  try List.rev vs with Stack_overflow ->
    Exhaustion.error at "call stack exhausted"

(*  Symbolic invoke  *)
(*
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
      Printf.printf "%s" (Logicenv.to_string logic_env);
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
            (Logicenv.to_string sym_st) ^
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
*)


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
  lines_to_ignore := List.((length elems) + (length data));
  let init_elems = List.map (init_table inst) elems in
  let init_datas = List.map (init_memory inst) data in
  List.iter (fun f -> f ()) init_elems;
  List.iter (fun f -> f ()) init_datas;
  Lib.Option.app (fun x -> ignore (sym_invoke' (func inst x) [])) start;
  inst
