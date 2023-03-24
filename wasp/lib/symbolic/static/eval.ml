open Encoding
open Expression
open Types
open Strategies
open Interpreter.Types
open Interpreter.Instance
open Interpreter.Ast

(* TODO/FIXME: there's a lot of code at the top that
  needs to be extracted to a common module with concolic.ml *)

(* Errors *)

module Link = Interpreter.Error.Make ()
module Trap = Interpreter.Error.Make ()
module Crash = Interpreter.Error.Make ()
module Exhaustion = Interpreter.Error.Make ()

exception Link = Link.Error
exception Trap = Trap.Error
exception Crash = Crash.Error (* failure that cannot happen in valid code *)
exception Exhaustion = Exhaustion.Error

let numeric_error at = function
  | Evaluations.UnsupportedOp m ->  m ^ ": unsupported operation"
  | Interpreter.Numeric_error.IntegerOverflow -> "integer overflow"
  | Interpreter.Numeric_error.IntegerDivideByZero -> "integer divide by zero"
  | Interpreter.Numeric_error.InvalidConversionToInteger ->
      "invalid conversion to integer"
  | Interpreter.Eval_numeric.TypeError (i, v, t) ->
    Crash.error at
      ("type error, expected " ^ Interpreter.Types.string_of_value_type t ^ " as operand " ^
       string_of_int i ^ ", got " ^ Interpreter.Types.string_of_value_type (Interpreter.Values.type_of v))
  | exn -> raise exn

(* Administrative Expressions & Configurations *)
type 'a stack = 'a list

let clone_frame (frame: sym_frame) : sym_frame =
  let sym_inst = clone frame.sym_inst in
  let sym_locals = List.map (fun r -> ref !r) frame.sym_locals in
  {
    sym_inst = sym_inst;
    sym_locals = sym_locals;
  }


(* Symbolic frame *)
let sym_frame sym_inst sym_locals = {sym_inst; sym_locals; }

exception BugException of bug * Interpreter.Source.region * string

let solver_counter = ref 0

let debug str = if !Interpreter.Flags.trace then print_endline str

let time_call f args acc =
  let start = Sys.time () in
  let ret = f args in
  acc := !acc +. ((Sys.time ()) -. start);
  ret

let plain (e : instr) : sym_admin_instr =
  let open Interpreter.Source in
  SPlain e.it @@ e.at

let lookup category list x =
  let open Interpreter.Source in
  try Interpreter.Lib.List32.nth list x.it with Failure _ ->
    Crash.error x.at ("undefined " ^ category ^ " " ^ Int32.to_string x.it)

let type_ (inst : module_inst) x = lookup "type" inst.types x
let func (inst : module_inst) x = lookup "function" inst.funcs x
let table (inst : module_inst) x = lookup "table" inst.tables x
let local (frame : sym_frame) x = lookup "local" frame.sym_locals x

let elem inst x i at =
  let open Interpreter in
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
  try Interpreter.Lib.List.take n vs with Failure _ ->
    Crash.error at "stack underflow"

let drop n (vs : 'a stack) at =
  try Interpreter.Lib.List.drop n vs with Failure _ ->
    Crash.error at "stack underflow"

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
    | SymAssert -> "sym_assert"
    | SymAssume -> "sym_assume"
    | Symbolic _ -> "symbolic"
    | _ -> "not support"

module type Encoder =
  sig
    type s
    type t = {
      solver : s;
      pc : pc ref
    }

    val time_solver : float ref

    val create : unit -> t
    val clone : t -> t

    val add : t -> expr -> unit
    val check : t -> expr list -> bool
    val fork : t -> expr -> bool * bool

    val value_binds :
      t -> (string * num_type) list -> (string * Num.t) list

    val string_binds :
      t -> (string * num_type) list -> (string * string * string) list
  end

module SymbolicInterpreter (SM : Memory.SymbolicMemory) (E : Encoder) : Interpreter =
  struct
    type sym_config = {
      sym_frame  : sym_frame;
      sym_code   : sym_code;
      sym_mem    : SM.t;
      sym_budget : int;  (* to model stack overflow *)
      var_map    : Varmap.t;
      sym_globals: Globals.t;
      chunk_table: (int32, int32) Hashtbl.t;
      encoder : E.t;
    }
    let rec clone_admin_instr e =
      let open Interpreter.Source in
      let it =
        match e.it with
        | SPlain e -> SPlain e
        | SInvoke f -> SInvoke f
        | STrapping exn -> STrapping exn
        | SReturning vs -> SReturning vs
        | SBreaking (n, vs) -> SBreaking (n, vs)
        | SLabel (n, es0, (vs, es)) ->
            SLabel (n, es0, (vs, List.map clone_admin_instr es))
        | SFrame (n, frame, (vs, es)) ->
            SFrame (n, clone_frame frame, (vs, List.map clone_admin_instr es))
        | Interrupt i -> Interrupt i
      in
      { it; at = e.at }
    let clone (c : sym_config) : sym_config * sym_config =
      let (vs, es) = c.sym_code in
      let sym_frame = clone_frame c.sym_frame in
      let sym_code = (vs, List.map clone_admin_instr es) in
      let sm, sym_mem = SM.clone c.sym_mem in
      let sym_budget = c.sym_budget in
      let var_map = Hashtbl.copy c.var_map in
      let sym_globals = Globals.clone_globals c.sym_globals in
      let chunk_table = Hashtbl.copy c.chunk_table in
      let encoder = E.clone c.encoder in
      {c with sym_mem = sm }, {
        sym_frame = sym_frame;
        sym_code = sym_code;
        sym_mem = sym_mem;
        sym_budget = sym_budget;
        var_map = var_map;
        sym_globals = sym_globals;
        chunk_table = chunk_table;
        encoder = encoder;
      }
    let sym_config
        (inst : module_inst)
        (vs : expr stack)
        (es : sym_admin_instr stack)
        (sym_m : Concolic.Heap.t)
        (globs : Globals.t)
        : sym_config = {
      sym_frame  = sym_frame inst [];
      sym_code   = vs, es;
      sym_mem    = SM.from_heap sym_m;
      sym_budget = 100000; (* models default recursion limit in a system *)
      var_map = Hashtbl.create Interpreter.Flags.hashtbl_default_size;
      sym_globals = globs;
      chunk_table = Hashtbl.create Interpreter.Flags.hashtbl_default_size;
      encoder = E.create ();
    }

    let time_solver = E.time_solver

    let memory_error at = function
      | SM.Bounds -> "out of bounds memory access"
      | Interpreter.Memory.SizeOverflow -> "memory size overflow"
      | Interpreter.Memory.SizeLimit -> "memory size limit reached"
      | Interpreter.Memory.Type ->
          Crash.error at "type mismatch at memory access"
      | exn -> raise exn

    let concretize_alloc (c : sym_config) : sym_config list =
      let {
        sym_code = vs, es;
        var_map = var_map;
        chunk_table = chunk_table;
        encoder = encoder;
        _} = c
      in
      let e, es' = match es with
      | e :: es' -> e, es'
      | _ -> failwith "unreachable"
      in
      let s_size, s_base, vs' = match vs with
      | s_size :: s_base :: vs' -> s_size, s_base, vs'
      | _ -> failwith "unreachable"
      in

      let helper (size : int32 option): sym_config option  =
        let size_cond = Option.map
          (function size ->
            Relop (I32 I32.Eq, s_size, Num (I32 size))
            ) size
        in
        let cond_list = match size_cond with
        | Some c -> [c]
        | None -> []
        in
        match E.check encoder cond_list with
        | false -> None
        | true -> begin
          let _, c = clone c in
          begin
            match size_cond with
            | Some size_cond -> E.add c.encoder size_cond
            | None -> ()
          end;
          let binds = E.value_binds c.encoder (Varmap.binds c.var_map)in
          let logic_env = Concolic.Store.create binds in

          let open Interpreter.Source in
          let c_size = Concolic.Store.eval logic_env s_size in
          let size = match c_size with
          | I32 size -> size
          | _ ->
            failwith ((Printf.sprintf "%d" e.at.left.line) ^ ":Alloc with non i32 size: " ^ Types.string_of_num_type (Types.type_of c_size));
          in
          let c_base = Concolic.Store.eval logic_env s_base in
          let base = match c_base with
          | I32 base -> base
          | _ ->
            failwith ((Printf.sprintf "%d" e.at.left.line) ^ ":Alloc with non i32 base: " ^ Types.string_of_num_type (Types.type_of c_base));
          in

          let base_cond = Relop (I32 I32.Eq, s_base, Num (I32 base)) in
          E.add c.encoder base_cond;
          Hashtbl.add c.chunk_table base size;

          let sym_ptr = SymPtr (base, (Num (I32 0l))) in
          Some { c with sym_code = sym_ptr :: List.tl vs, List.tl es }
          end
      in

      (* TODO: add flag to configure these *)
      let fixed_numbers = [0l; 1l; 2l; 4l; 8l; 256l; 4096l] in
      let fixed_attempts = List.filter_map helper
        (List.map Option.some fixed_numbers) in
      if List.length fixed_attempts > 0 then
        fixed_attempts
      else
        [Option.get (helper None)]

    let rec step (c : sym_config) : ((sym_config list * pc list), string * string) result =
      let {
        sym_frame = frame;
        sym_code = vs, es;
        sym_mem = mem;
        var_map = var_map;
        chunk_table = chunk_table;
        encoder = encoder;
        _} = c in
      let open Interpreter in
      let open Source in
      match es with
      | [] -> begin
        let open E in
        Result.ok ([], [!(encoder.pc)])
      end
      | e :: t ->
      (match e.it, vs with
        | SPlain e', vs ->
          (match e', vs with
          | Nop, vs ->
            Result.ok ([ { c with sym_code = vs, List.tl es } ], [])

          | Drop, v :: vs' ->
            Result.ok ([ { c with sym_code = vs', List.tl es } ], [])

          | Select, ex :: v2 :: v1 :: vs' ->
            (match simplify ex with
            | Num (I32 0l) ->
              (* if it is 0 *)
              Result.ok ([ { c with sym_code = v2 :: vs', List.tl es } ], [])
            | Num (I32 _) ->
              (* if it is not 0 *)
              Result.ok ([ { c with sym_code = v1 :: vs', List.tl es } ], [])
            | ex -> (
              let co = Option.get (to_relop ex) in
              let negated_co = negate_relop co in
              let es' = List.tl es in

              solver_counter := !solver_counter + 2;
              let sat_then, sat_else = E.fork encoder co in

              let l = match (sat_then, sat_else) with
              | (true, true) ->
                let c, c_clone = clone c in
                E.add c.encoder co;
                E.add c_clone.encoder negated_co;
                [{ c with sym_code = v1 :: vs', es' }
                ;{ c_clone with sym_code = v2 :: vs', es' }]
              | (true, false) ->
                E.add encoder co;
                [{ c with sym_code = v1 :: vs', es' }]
              | (false, true) ->
                E.add encoder negated_co;
                [{ c with sym_code = v2 :: vs', es' }]
              | (false, false) -> failwith "Unreachable Select"
              in

              Result.ok (l, [])
              )
            )

          | Block (ts, es'), vs ->
            let es0 = SLabel (List.length ts, [], ([], List.map plain es')) @@ e.at in
            Result.ok ([ { c with sym_code = vs, es0 :: (List.tl es) } ], [])

          | Loop (ts, es'), vs ->
            let es0 = SLabel (0, [e' @@ e.at], ([], List.map plain es')) @@ e.at in
            Result.ok ([ { c with sym_code = vs, es0 :: (List.tl es) } ], [])

          | If (ts, es1, es2), ex :: vs' ->
            (let es' = List.tl es in
            match simplify ex with
            | Num (I32 0l) ->
              (* if it is 0 *)
              Result.ok ([ { c with sym_code = vs', [SPlain (Block (ts, es2)) @@ e.at] @ es' } ], [])
            | Num (I32 _) ->
              (* if it is not 0 *)
              Result.ok ([ { c with sym_code = vs', [SPlain (Block (ts, es1)) @@ e.at] @ es' } ], [])
            | ex -> (
              let co = Option.get (to_relop ex) in
              let negated_co = negate_relop co in

              solver_counter := !solver_counter + 2;
              let sat_then, sat_else = E.fork encoder co in

              let l = match (sat_then, sat_else) with
              | (true, true) ->
                let c, c_clone = clone c in
                E.add c.encoder co;
                E.add c_clone.encoder negated_co;
                [{ c with sym_code = vs', [SPlain (Block (ts, es1)) @@ e.at] @ es'  }
                ;{ c_clone with sym_code = vs', [SPlain (Block (ts, es2)) @@ e.at] @ es' }]
              | (true, false) ->
                E.add encoder co;
                [{ c with sym_code = vs', [SPlain (Block (ts, es1)) @@ e.at] @ es'  }]
              | (false, true) ->
                E.add encoder negated_co;
                [{ c with sym_code = vs', [SPlain (Block (ts, es2)) @@ e.at] @ es'  }]
              | (false, false) -> failwith "Unreachable If"
              in

              Result.ok (l, [])
              )
            )

          | Br x, vs ->
            Result.ok ([ { c with sym_code = vs, [SBreaking (x.it, vs) @@ e.at] } ], [])

          | BrIf x, ex :: vs' ->
            (match simplify ex with
            | Num (I32 0l) ->
              (* if it is 0 *)
              let es' = List.tl es in
              Result.ok ([ { c with sym_code = vs', es' } ], [])
            | Num (I32 _) ->
              (* if it is not 0 *)
              Result.ok ([ { c with sym_code = vs', [SPlain (Br x) @@ e.at] } ], [])
            | ex -> (
              let co = Option.get (to_relop ex) in
              let negated_co = negate_relop co in
              let es' = List.tl es in

              solver_counter := !solver_counter + 2;
              let sat_then, sat_else = E.fork encoder co in

              let l = match (sat_then, sat_else) with
              | (true, true) ->
                let c, c_clone = clone c in
                E.add c.encoder co;
                E.add c_clone.encoder negated_co;
                [{ c with sym_code = vs', [SPlain (Br x) @@ e.at] }
                ;{ c_clone with sym_code = vs', es' }]
              | (true, false) ->
                E.add encoder co;
                [{ c with sym_code = vs', [SPlain (Br x) @@ e.at] }]
              | (false, true) ->
                E.add encoder negated_co;
                [{ c with sym_code = vs', es' }]
              | (false, false) -> failwith "Unreachable BrIf"
              in

              Result.ok (l, [])
              )
            )

          | Return, vs ->
            let es' = [SReturning vs @@ e.at] @ List.tl es in
            Result.ok ([{c with sym_code = [], es'}], [])

          | Call x, vs ->
            Result.ok ([ { c with sym_code = vs, [SInvoke (func frame.sym_inst x) @@ e.at] @ t } ], [])

          | CallIndirect x, Num (I32 i) :: vs ->
            let func = func_elem frame.sym_inst (0l @@ e.at) i e.at in
            let es' = if type_ frame.sym_inst x <> Func.type_of func then
              [STrapping "indirect call type mismatch" @@ e.at]
            else
              [SInvoke func @@ e.at] in
            Result.ok ([{c with sym_code = vs, es' @ List.tl es}], [])

          | LocalGet x, vs ->
            let vs' = !(local frame x) :: vs in
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = vs', es' } ], [])

          | LocalSet x, v :: vs' ->
            local frame x := v;
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = vs', es' } ], [])

          | LocalTee x, v :: vs' ->
            local frame x := v;
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = v :: vs', es' } ], [])

          | GlobalGet x, vs ->
            let v' = Globals.load c.sym_globals x.it in
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = v' :: vs, es' } ], [])

          | GlobalSet x, v :: vs' ->
            let es' = List.tl es in
            (try
              Globals.store c.sym_globals x.it v;
              Result.ok ([ { c with sym_code = vs', es' } ], [])
            with  Global.NotMutable -> Crash.error e.at "write to immutable global"
                | Global.Type -> Crash.error e.at "type mismatch at global write")

          | Load {offset; ty; sz; _}, sym_ptr :: vs' ->
            let sym_ptr = simplify sym_ptr in
            let ptr = match concretize_ptr sym_ptr with
            | Some ptr -> ptr
            | None -> begin
              let binds = E.value_binds encoder (Varmap.binds var_map) in
              let logic_env = Concolic.Store.create binds in

              let ptr = Concolic.Store.eval logic_env sym_ptr in
              let ty = Encoding.Types.type_of ptr in
              if ty <> I32Type then
                failwith ((Printf.sprintf "%d" e.at.left.line) ^ ":Load with non i32 ptr: " ^ Encoding.Types.string_of_num_type ty);

              let ptr_cond = Relop (I32 Encoding.Types.I32.Eq, sym_ptr, Num ptr) in
              E.add encoder ptr_cond;

              (* TODO: generate a configuration equal to the original with the condition denied in the path_cond ? *)
              ptr
            end
            in
            let ptr64 = I64_convert.extend_i32_u (Values.I32Value.of_value (Evaluations.to_value ptr)) in
            let base_ptr = concretize_base_ptr sym_ptr in
            begin try
              if Option.is_some base_ptr then begin
                let low = Option.get base_ptr in
                let chunk_size =
                  try Hashtbl.find chunk_table low
                  with Not_found -> raise (BugException (UAF, e.at, "")) in
                let high = Int64.(add (of_int32 low) (of_int32 chunk_size)) in
                let ptr_i64 = Int64.of_int32 (Values.I32Value.of_value (Evaluations.to_value ptr)) in
                let ptr_val = Int64.(add ptr_i64 (of_int32 offset)) in
                (* ptr_val \notin [low, high] => overflow *)
                if ptr_val < (Int64.of_int32 low) || ptr_val >= high then
                  raise (BugException (Overflow, e.at, ""))
              end;
              let v =
                match sz with
                | None         ->
                    SM.load_value mem ptr64 offset (Evaluations.to_num_type ty)
                | Some (sz, _) ->
                    SM.load_packed sz mem ptr64 offset (Evaluations.to_num_type ty)
              in
              let es' = List.tl es in
              Result.ok ([ { c with sym_code = v :: vs', es' } ], [])
            with
            | BugException (b, at, _) ->
              let string_binds = E.string_binds encoder (Varmap.binds var_map) in
              let witness = Concolic.Store.strings_to_json string_binds in
              let bug_type = match b with
              | Overflow -> "Out of Bounds access"
              | UAF -> "Use After Free"
              | _ -> failwith "unreachable, other bugs shouldn't be here"
              in
              let reason = "{" ^
              "\"type\" : \"" ^ bug_type ^ "\", " ^
              "\"line\" : \"" ^ (string_of_pos e.at.left ^
                  (if e.at.right = e.at.left then "" else "-" ^ string_of_pos e.at.right)) ^ "\"" ^
              "}"
              in
              Result.error (reason, witness)
            | exn ->
              Result.ok ([ { c with sym_code = vs', [STrapping (memory_error e.at exn) @@ e.at] } ], [])
            end

          | Store {offset; sz; _}, ex :: sym_ptr :: vs' ->
            let sym_ptr = simplify sym_ptr in
            let ptr = match concretize_ptr sym_ptr with
            | Some ptr -> ptr
            | None -> begin
              let binds = E.value_binds encoder (Varmap.binds var_map)in
              let logic_env = Concolic.Store.create binds in

              let ptr = Concolic.Store.eval logic_env sym_ptr in
              let ty = Encoding.Types.type_of ptr in
              if ty <> I32Type then
                failwith ((Printf.sprintf "%d" e.at.left.line) ^ ":Store with non i32 ptr: " ^ Encoding.Types.string_of_num_type ty);

              let ptr_cond = Relop (I32 Encoding.Types.I32.Eq, sym_ptr, Num ptr) in
              E.add encoder ptr_cond;

              (* TODO: generate a configuration equal to the original with the condition denied in the path_cond ? *)
              ptr
            end
            in
            let ptr64 = I64_convert.extend_i32_u (Values.I32Value.of_value (Evaluations.to_value ptr)) in
            let base_ptr = concretize_base_ptr sym_ptr in
            begin try
              if Option.is_some base_ptr then begin
                let low = Option.get base_ptr in
                let chunk_size =
                  try Hashtbl.find chunk_table low
                  with Not_found -> raise (BugException (UAF, e.at, "")) in
                let high = Int64.(add (of_int32 low) (of_int32 chunk_size)) in
                let ptr_i64 = Int64.of_int32 (Values.I32Value.of_value (Evaluations.to_value ptr)) in
                let ptr_val = Int64.(add ptr_i64 (of_int32 offset)) in
                (* ptr_val \notin [low, high[ => overflow *)
                if ptr_val < (Int64.of_int32 low) || ptr_val >= high then
                  raise (BugException (Overflow, e.at, ""))
              end;
              begin match sz with
              | None    -> SM.store_value mem ptr64 offset ex
              | Some sz -> SM.store_packed sz mem ptr64 offset ex
              end;
              let es' = List.tl es in
              Result.ok ([ { c with sym_code = vs', es' } ], [])
            with
            | BugException (b, at, _) ->
              let string_binds = E.string_binds encoder (Varmap.binds var_map) in
              let witness = Concolic.Store.strings_to_json string_binds in
              let bug_type = match b with
              | Overflow -> "Out of Bounds access"
              | UAF -> "Use After Free"
              | _ -> failwith "unreachable, other bugs shouldn't be here"
              in
              let reason = "{" ^
              "\"type\" : \"" ^ bug_type ^ "\", " ^
              "\"line\" : \"" ^ (string_of_pos e.at.left ^
                  (if e.at.right = e.at.left then "" else "-" ^ string_of_pos e.at.right)) ^ "\"" ^
              "}"
              in
              Result.error (reason, witness)
            | exn ->
              Result.ok ([ { c with sym_code = vs', [STrapping (memory_error e.at exn) @@ e.at] } ], [])
            end

          | Const v, vs ->
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = (Num (Evaluations.of_value v.it)) :: vs, es' } ], [])

          | Test testop, v :: vs' ->
            let es' = List.tl es in
            (try
              let v' = Evaluations.eval_testop v testop in
              Result.ok ([ { c with sym_code = simplify v' :: vs', es' } ], [])
            with exn ->
              Result.ok ([ { c with sym_code = vs', (STrapping (numeric_error e.at exn) @@ e.at) :: es' } ], []))

          | Compare relop, v2 :: v1 :: vs' ->
            let es' = List.tl es in
            (try
              let v = Evaluations.eval_relop v1 v2 relop in
              Result.ok ([ { c with sym_code = simplify v :: vs', es' } ], [])
            with exn ->
              Result.ok ([ { c with sym_code = vs', (STrapping (numeric_error e.at exn) @@ e.at) :: es' } ], []))

          | Unary unop, v :: vs' ->
            let es' = List.tl es in
            (try
              let v = Evaluations.eval_unop v unop in
              Result.ok ([ { c with sym_code = simplify v :: vs', es' } ], [])
            with exn ->
              Result.ok ([ { c with sym_code = vs', (STrapping (numeric_error e.at exn) @@ e.at) :: es' } ], []))

          | Binary binop, v2 :: v1 :: vs' ->
            let es' = List.tl es in
            (try
              let v = Evaluations.eval_binop v1 v2 binop in
              Result.ok ([ { c with sym_code = simplify v :: vs', es' } ], [])
            with exn ->
              Result.ok ([ { c with sym_code = vs', (STrapping (numeric_error e.at exn)  @@ e.at) :: es' } ], []))

          | Convert cvtop, v :: vs' ->
            let es' = List.tl es in
            (try
              let v' = Evaluations.eval_cvtop cvtop v in
              Result.ok ([ { c with sym_code = simplify v' :: vs', es' } ], [])
            with exn ->
              Result.ok ([ { c with sym_code = vs', (STrapping (numeric_error e.at exn)  @@ e.at) :: es' } ], []))

          | Dup, v :: vs' ->
            let vs'' = v :: v :: vs' in
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = (vs'', es') } ], [])

          | GetSymInt32 x, vs' ->
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = (Symbolic (I32Type, x)) :: vs', es'} ], [])

          | GetSymInt64 x, vs' ->
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = (Symbolic (I64Type, x)) :: vs', es'} ], [])

          | GetSymFloat32 x, vs' ->
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = (Symbolic (F32Type, x)) :: vs', es'} ], [])

          | GetSymFloat64 x, vs' ->
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = (Symbolic (F64Type, x)) :: vs', es'} ], [])

          | SymAssert, Num (I32 0l) :: vs' ->
            debug (string_of_pos e.at.left ^ ":Assert FAILED! Stopping...");
            let string_binds = E.string_binds encoder (Varmap.binds var_map) in
            let witness = Concolic.Store.strings_to_json string_binds in
            let reason = "{" ^
            "\"type\" : \"" ^ "Assertion Failure" ^ "\", " ^
            "\"line\" : \"" ^ (string_of_pos e.at.left ^
                (if e.at.right = e.at.left then "" else "-" ^ string_of_pos e.at.right)) ^ "\"" ^
            "}"
            in
            Result.error (reason, witness)

          | SymAssert, Num (I32 i) :: vs' ->
            (* passed *)
            debug (string_of_pos e.at.left ^ ":Assert PASSED!");
            Result.ok ([ { c with sym_code = vs', List.tl es } ], [])

          | SymAssert, v :: vs' ->
            let v = simplify v in
            debug ("Asserting: " ^ to_string (simplify v));
            let opt_witness =
              let c = negate_relop (Option.get (to_relop v)) in
              solver_counter := !solver_counter + 1;
              let sat = E.check encoder [ c ] in
              if sat then
                let string_binds = E.string_binds encoder (Varmap.binds var_map) in
                let witness = Concolic.Store.strings_to_json string_binds in
                Some witness
              else
                None
            in
            if Option.is_some opt_witness then
              debug (string_of_pos e.at.left ^ ":Assert FAILED! Stopping...")
            else
              debug (string_of_pos e.at.left ^ ":Assert PASSED!");
            (match opt_witness with
            | Some c -> (
              let reason = "{" ^
              "\"type\" : \"" ^ "Assertion Failure" ^ "\", " ^
              "\"line\" : \"" ^ (string_of_pos e.at.left ^
                  (if e.at.right = e.at.left then "" else "-" ^ string_of_pos e.at.right)) ^ "\"" ^
              "}"
              in
              Result.error (reason, c)
              )
            | None -> Result.ok ([ { c with sym_code = (vs', List.tl es) } ], [])
            )

          | SymAssume, ex :: vs' ->
            (match simplify ex with
            | Num (I32 0l) ->
              (* if it is 0 *)
              Result.ok ([], [])
            | SymPtr (_, Num (I32 0l))
            | Num (I32 _) ->
              (* if it is not 0 *)
              Result.ok ([ { c with sym_code = vs, List.tl es } ], [])
            | ex -> (
              let co = Option.get (to_relop ex) in
              solver_counter := !solver_counter + 1;
              E.add encoder co;
              if E.check encoder [] then
                let c_true = { c with sym_code = vs', List.tl es } in
                Result.ok ([ c_true ], []);
              else
                Result.ok ([], [])
              )
            )

          | Symbolic (ty, b), (Num (I32 i)) :: vs' ->
            let base = I64_convert.extend_i32_u i in
            let symbol = if i = 0l then "x" else SM.load_string mem base in
            let x = Varmap.next symbol in
            let ty' = Evaluations.to_num_type ty in
            let v = symbolic ty' x in
            let es' = List.tl es in
            Hashtbl.replace var_map x ty';
            Result.ok ([ { c with sym_code = (v :: vs', es') } ], [])

          | Boolop boolop, v1 :: v2 :: vs' ->
            (* results in i32 *)
            let v2' = mk_relop v2 I32Type in
            let v1' = mk_relop v1 I32Type in
            let v3 = Evaluations.eval_binop v1' v2' boolop in
            let es' = List.tl es in
            (try
              Result.ok ([ { c with sym_code = (simplify v3 :: vs', es') } ], [])
            with exn ->
              Result.ok ([ { c with sym_code = vs', (STrapping (numeric_error e.at exn) @@ e.at) :: es' } ], [])
            )

          | Alloc, Num (I32 sz) :: Num (I32 base) :: vs' ->
            Hashtbl.add chunk_table base sz;
            let sym_ptr = SymPtr (base, (Num (I32 0l))) in
            Result.ok ([{c with sym_code = sym_ptr :: vs', List.tl es}], [])

          | Alloc, _ :: _ :: vs' ->
            Result.ok (concretize_alloc c, [])

          | Free, ptr :: vs' -> (
            match simplify ptr with
            | SymPtr (base, (Num (I32 0l))) ->
              let es' =
                if not (Hashtbl.mem chunk_table base) then (
                  let string_binds = E.string_binds encoder (Varmap.binds var_map) in
                  let witness = Concolic.Store.strings_to_json string_binds in
                  [Interrupt (Bug (InvalidFree, witness)) @@ e.at] @ List.tl es
                ) else (
                  Hashtbl.remove chunk_table base;
                  List.tl es
                )
              in
              Result.ok ([{c with sym_code = vs', es'}], [])
            | value ->
              failwith ("Free with invalid argument" ^ (pp_to_string value))
          )

          | PrintStack, vs ->
            let vs' = List.map (fun v -> (pp_to_string v)) vs in
            print_endline ("Stack:" ^ "\n" ^ (String.concat "\n" vs'));
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = vs, es' } ], [])

          | PrintMemory, vs ->
            print_endline ("Memory State:\n" ^ (SM.to_string mem));
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = vs, es' } ], [])

          | PrintPC, vs ->
            let open E in
            let assertion = Encoding.Formula.to_formula !(encoder.pc) in
            print_endline ((Printf.sprintf "%d" e.at.left.line) ^ " pc: " ^ (Encoding.Formula.pp_to_string assertion));
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = vs, es' } ], [])

          | PrintValue, v:: vs' ->
            let es' = List.tl es in
            print_endline ((Printf.sprintf "%d" e.at.left.line) ^ ":val: " ^ pp_to_string v);
            Result.ok ([ { c with sym_code = vs, es' } ], [])

          | _ -> (
            print_endline ((string_of_region e.at) ^ ":Not implemented " ^ instr_str e');
            let reason = "{" ^
            "\"type\" : \"" ^ "Not implemented" ^ "\", " ^
            "\"line\" : \"" ^ (string_of_pos e.at.left ^
                (if e.at.right = e.at.left then "" else "-" ^ string_of_pos e.at.right)) ^ "\"" ^
            "}"
            in
            Result.error (reason, "[]")
            )
          )

      | SLabel (n, es0, (vs', [])), vs ->
        Result.ok ([ { c with sym_code = vs' @ vs, List.tl es } ], [])

      | SLabel (n, es0, (vs', {it = Interrupt i; at} :: es')), vs ->
        let es' = (Interrupt i @@ at) :: [SLabel (n, es0, (vs', es')) @@ e.at] in
        Result.ok ([ { c with sym_code = vs, es' @ (List.tl es) } ], [])

      | SLabel (n, es0, (vs', {it = STrapping msg; at} :: es')), vs ->
        (* TODO *)
        Trap.error e.at "trap"

      | SLabel (n, es0, (vs', {it = SReturning vs0; at} :: es')), vs ->
        let vs'' = take n vs0 e.at @ vs in
        Result.ok ([ { c with sym_code = vs'', List.tl es } ], [])

      | SLabel (n, es0, (vs', {it = SBreaking (0l, vs0); at} :: es')), vs ->
        let vs'' = take n vs0 e.at @ vs in
        let es' = List.map plain es0 in
        Result.ok ([ { c with sym_code = vs'', es' @ (List.tl es) } ], [])

      | SLabel (n, es0, (vs', {it = SBreaking (k, vs0); at} :: es')), vs ->
        let es0' = SBreaking (Int32.sub k 1l, vs0) @@ at in
        Result.ok ([ { c with sym_code = vs, es0' :: (List.tl es) } ], [])

      | SLabel (n, es0, code'), vs ->
        (* FIXME: path conditions *)
        Result.map (fun (cs', outs') ->
          (List.map (fun c ->
            let es0' = SLabel (n, es0, c.sym_code) @@ e.at in
            { c with sym_code = vs, es0' :: (List.tl es) })
          cs', outs')) (step {c with sym_code = code'})

      | SFrame (n, frame', (vs', [])), vs ->
        Result.ok ([ { c with sym_code = vs' @ vs, List.tl es } ], [])

      | SFrame (n, frame', (vs', {it = Interrupt i; at} :: es')), vs ->
        let es' = (Interrupt i @@ at) :: [SFrame (n, frame', (vs', es')) @@ e.at] in
        Result.ok ([ { c with sym_code = vs, es' @ (List.tl es) } ], [])

      | SFrame (n, frame', (vs', {it = STrapping msg; at} :: es')), vs ->
        (* TODO *)
        Trap.error e.at "trap"

      | SFrame (n, frame', (vs', {it = SReturning vs0; at} :: es')), vs ->
        let vs'' = take n vs0 e.at @ vs in
        Result.ok ([ { c with sym_code = vs'', List.tl es } ], [])

      | SFrame (n, frame', code'), vs ->
        Result.map (fun (cs', outs') ->
          (List.map (fun (c' : sym_config) ->
            let es0 = SFrame (n, c'.sym_frame, c'.sym_code) @@ e.at in
            { c' with sym_code = vs, es0 :: (List.tl es); sym_frame = (clone_frame frame) }
          ) cs', outs')
        ) (step {
          sym_frame = frame';
          sym_code = code';
          sym_mem = c.sym_mem;
          sym_budget = c.sym_budget - 1;
          var_map = c.var_map;
          sym_globals = c.sym_globals;
          chunk_table = c.chunk_table;
          encoder = c.encoder;
        })

      | STrapping msg, vs ->
        assert false

      | Interrupt i, vs ->
        assert false

      | SReturning vs', vs ->
        Crash.error e.at "undefined frame"

      | SBreaking (k, vs'), vs ->
        Crash.error e.at "undefined label"

      | SInvoke func, vs when c.sym_budget = 0 ->
        Exhaustion.error e.at "call stack exhausted"

      | SInvoke func, vs ->
          let FuncType (ins, out) = Func.type_of func in
          let n = List.length ins in
          let args, vs' = take n vs e.at, drop n vs e.at in
          (match func with
          | Func.AstFunc (t, inst', f) ->
            let locals' =
              List.map (fun v -> Num v)
                (List.map
                  (fun t -> Num.default_value (Evaluations.to_num_type t))
                  f.it.locals) in
            let locals'' = List.rev args @ locals' in
            let code' = [], [SPlain (Block (out, f.it.body)) @@ f.at] in
            let frame' = {sym_inst = !inst'; sym_locals = List.map ref locals''} in
            let es0 = (SFrame (List.length out, frame', code') @@ e.at) in
            Result.ok ([ { c with sym_code = vs', es0 :: (List.tl es) } ], [])

          | Func.HostFunc (t, f) ->
            failwith "HostFunc error"
          )
      )
  end

module EncodingSelector (SM : Memory.SymbolicMemory) = struct
  module SI_SM = SymbolicInterpreter(SM)

  module BatchHelper = Strategies.Helper(SI_SM(Encoding.Batch))
  module IncrementalHelper = Strategies.Helper(SI_SM(Encoding.Incremental))

  let parse_encoding () =
    match !Interpreter.Flags.encoding with
    | "batch" -> BatchHelper.helper
    | "incremental" -> IncrementalHelper.helper
    | _ -> failwith "Invalid encoding option"
end

module MapMem_EncondingSelector = EncodingSelector(Memory.MapSMem)
module LazyMem_EncondingSelector = EncodingSelector(Memory.LazySMem)
module TreeMem_EncondingSelector = EncodingSelector(Memory.TreeSMem)

let parse_memory_and_encoding () =
  match !Interpreter.Flags.memory with
  | "map" -> MapMem_EncondingSelector.parse_encoding ()
  | "lazy" -> LazyMem_EncondingSelector.parse_encoding ()
  | "tree" -> TreeMem_EncondingSelector.parse_encoding ()
  | _ -> failwith "Invalid memory backend"

let func_to_globs (func : func_inst): Globals.t =
  match Interpreter.Func.get_inst func with
  | Some inst -> Globals.from_list (!inst).globals
  | None -> Hashtbl.create 0

let invoke (func : func_inst) (vs : expr list) (mem0 : Concolic.Heap.t)
    : unit =
  let open Interpreter in
  let open Source in
  let at = match func with Func.AstFunc (_, _, f) -> f.at | _ -> no_region in
  (* extract globals to symbolic config *)
  let globs = func_to_globs func in
  let helper = parse_memory_and_encoding () in
  let (spec, reason, witness, loop_time, solver_time, paths) = helper empty_module_inst (List.rev vs) [SInvoke func @@ at]
    mem0 globs in

  Io.safe_mkdir !Flags.output;

  (* Execution report *)
  let fmt_str = "{" ^
    "\"specification\": "        ^ (string_of_bool spec)          ^ ", " ^
    "\"reason\" : "              ^ reason                         ^ ", " ^
    "\"witness\" : "             ^ witness                        ^ ", " ^
    (* "\"coverage\" : \""          ^ (string_of_float coverage)     ^ "\", " ^ *)
    "\"loop_time\" : \""         ^ (string_of_float loop_time)    ^ "\", " ^
    "\"solver_time\" : \""       ^ (string_of_float solver_time) ^ "\", " ^
    "\"paths_explored\" : "      ^ (string_of_int paths)    ^ ", " ^
    "\"solver_counter\" : "      ^ (string_of_int !solver_counter)    ^ (*", " ^*)
    (* "\"instruction_counter\" : " ^ (string_of_int !step_cnt)      ^ ", " ^ *)
    (* "\"incomplete\" : "          ^ (string_of_bool !incomplete)   ^ *)
  "}"
  in Io.save_file (Filename.concat !Flags.output "report.json") fmt_str;

