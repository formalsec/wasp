open Values
open Symvalue
open Types
open Instance
open Ast
open Strategies

(* TODO/FIXME: there's a lot of code at the top that
  needs to be extracted to a common module with concolic.ml *)

(* Errors *)

module Link = Error.Make ()
module Trap = Error.Make ()
module Crash = Error.Make ()
module Exhaustion = Error.Make ()

exception Link = Link.Error
exception Trap = Trap.Error
exception Crash = Crash.Error (* failure that cannot happen in valid code *)
exception Exhaustion = Exhaustion.Error

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

exception BugException of bug * Source.region * string

let solver_counter = ref 0

let debug str = if !Flags.trace then print_endline str

let time_call f args acc =
  let start = Sys.time () in
  let ret = f args in
  acc := !acc +. ((Sys.time ()) -. start);
  ret

let plain (e : instr) : sym_admin_instr =
  let open Source in
  SPlain e.it @@ e.at

let lookup category list x =
  let open Source in
  try Lib.List32.nth list x.it with Failure _ ->
    Crash.error x.at ("undefined " ^ category ^ " " ^ Int32.to_string x.it)

let type_ (inst : module_inst) x = lookup "type" inst.types x
let func (inst : module_inst) x = lookup "function" inst.funcs x
let table (inst : module_inst) x = lookup "table" inst.tables x
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
      pc : path_conditions ref
    }

    val time_solver : float ref

    val create : unit -> t
    val clone : t -> t

    val add : t -> sym_expr -> unit
    val check : t -> sym_expr list -> bool
    val fork : t -> sym_expr -> bool * bool

    val value_binds :
      t -> (string * Types.value_type) list -> (string * value) list

    val string_binds :
      t -> (string * Types.value_type) list -> (string * string * string) list
  end

module SymbolicExecutor (E : Encoder) (SM : Symmem.SymbolicMemory) : EncodingStrategy =
  struct
    type sym_config = {
      sym_frame  : sym_frame;
      sym_code   : sym_code;
      sym_mem    : SM.t;
      sym_budget : int;  (* to model stack overflow *)
      var_map    : Varmap.t;
      sym_globals: Static_globals.t;
      chunk_table: (int32, int32) Hashtbl.t;
      encoder : E.t;
    }
    let clone (c : sym_config) : sym_config * sym_config =
      let sym_frame = clone_frame c.sym_frame in
      let sym_code = c.sym_code in
      let sm, sym_mem = SM.clone c.sym_mem in
      let sym_budget = c.sym_budget in
      let var_map = Hashtbl.copy c.var_map in
      let sym_globals = Static_globals.clone_globals c.sym_globals in
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
        (vs : sym_expr stack)
        (es : sym_admin_instr stack)
        (sym_m : Heap.t)
        (globs : Static_globals.t)
        : sym_config = {
      sym_frame  = sym_frame inst [];
      sym_code   = vs, es;
      sym_mem    = SM.from_heap sym_m;
      sym_budget = 100000; (* models default recursion limit in a system *)
      var_map = Hashtbl.create 100;
      sym_globals = globs;
      chunk_table = Hashtbl.create 512;
      encoder = E.create ();
    }

    let time_solver = E.time_solver

    let memory_error at = function
      | SM.Bounds -> "out of bounds memory access"
      | Memory.SizeOverflow -> "memory size overflow"
      | Memory.SizeLimit -> "memory size limit reached"
      | Memory.Type -> Crash.error at "type mismatch at memory access"
      | exn -> raise exn

    let rec step (c : sym_config) : ((sym_config list * path_conditions list), string * string) result =
      let {
        sym_frame = frame;
        sym_code = vs, es;
        sym_mem = mem;
        var_map = var_map;
        chunk_table = chunk_table;
        encoder = encoder;
        _} = c in
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
            | Value (I32 0l) ->
              (* if it is 0 *)
              Result.ok ([ { c with sym_code = v2 :: vs', List.tl es } ], [])
            | Value (I32 _) ->
              (* if it is not 0 *)
              Result.ok ([ { c with sym_code = v1 :: vs', List.tl es } ], [])
            | ex -> (
              let co = Option.get (Symvalue.to_constraint ex) in
              let negated_co = Symvalue.negate_relop co in
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
            | Value (I32 0l) ->
              (* if it is 0 *)
              Result.ok ([ { c with sym_code = vs', [SPlain (Block (ts, es2)) @@ e.at] @ es' } ], [])
            | Value (I32 _) ->
              (* if it is not 0 *)
              Result.ok ([ { c with sym_code = vs', [SPlain (Block (ts, es1)) @@ e.at] @ es' } ], [])
            | ex -> (
              let co = Option.get (to_constraint ex) in
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
            | Value (I32 0l) ->
              (* if it is 0 *)
              let es' = List.tl es in
              Result.ok ([ { c with sym_code = vs', es' } ], [])
            | Value (I32 _) ->
              (* if it is not 0 *)
              Result.ok ([ { c with sym_code = vs', [SPlain (Br x) @@ e.at] } ], [])
            | ex -> (
              let co = Option.get (to_constraint ex) in
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

          | CallIndirect x, Value (I32 i) :: vs ->
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
            let v' = Static_globals.load c.sym_globals x.it in
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = v' :: vs, es' } ], [])

          | GlobalSet x, v :: vs' ->
            let es' = List.tl es in
            (try
              Static_globals.store c.sym_globals x.it v;
              Result.ok ([ { c with sym_code = vs', es' } ], [])
            with  Global.NotMutable -> Crash.error e.at "write to immutable global"
                | Global.Type -> Crash.error e.at "type mismatch at global write")

          | Load {offset; ty; sz; _}, sym_ptr :: vs' ->
            let sym_ptr = simplify sym_ptr in
            let ptr = match concretize_ptr sym_ptr with
            | Some ptr -> ptr
            | None -> begin
              let binds = E.value_binds encoder (Varmap.binds var_map) in
              let logic_env = Store.create binds in

              let ptr = Store.eval logic_env sym_ptr in
              let ty = Values.type_of ptr in
              if ty != I32Type then
                failwith ((Printf.sprintf "%d" e.at.left.line) ^ ":Load with non i32 ptr: " ^ Types.string_of_value_type ty);

              let ptr_cond = Symvalue.I32Relop (Si32.I32Eq, sym_ptr, Value ptr) in
              E.add encoder ptr_cond;

              (* TODO: generate a configuration equal to the original with the condition denied in the path_cond ? *)
              ptr
            end
            in
            let ptr64 = I64_convert.extend_i32_u (I32Value.of_value ptr) in
            let base_ptr = concretize_base_ptr sym_ptr in
            begin try
              if Option.is_some base_ptr then begin
                let low = Option.get base_ptr in
                let chunk_size =
                  try Hashtbl.find chunk_table low
                  with Not_found -> raise (BugException (UAF, e.at, "")) in
                let high = Int64.(add (of_int32 low) (of_int32 chunk_size)) in
                let ptr_i64 = Int64.of_int32 (I32Value.of_value ptr) in
                let ptr_val = Int64.(add ptr_i64 (of_int32 offset)) in
                (* ptr_val \notin [low, high] => overflow *)
                if ptr_val < (Int64.of_int32 low) || ptr_val >= high then
                  raise (BugException (Overflow, e.at, ""))
              end;
              let v =
                match sz with
                | None         -> SM.load_value mem ptr64 offset ty
                | Some (sz, _) -> SM.load_packed sz mem ptr64 offset ty
              in
              let es' = List.tl es in
              Result.ok ([ { c with sym_code = v :: vs', es' } ], [])
            with
            | BugException (b, at, _) ->
              let string_binds = E.string_binds encoder (Varmap.binds var_map) in
              let witness = Store.strings_to_json string_binds in
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
              let logic_env = Store.create binds in

              let ptr = Store.eval logic_env sym_ptr in
              let ty = Values.type_of ptr in
              if ty != I32Type then
                failwith ((Printf.sprintf "%d" e.at.left.line) ^ ":Store with non i32 ptr: " ^ Types.string_of_value_type ty);

              let ptr_cond = Symvalue.I32Relop (Si32.I32Eq, sym_ptr, Value ptr) in
              E.add encoder ptr_cond;

              (* TODO: generate a configuration equal to the original with the condition denied in the path_cond ? *)
              ptr
            end
            in
            let ptr64 = I64_convert.extend_i32_u (I32Value.of_value ptr) in
            let base_ptr = concretize_base_ptr sym_ptr in
            begin try
              if Option.is_some base_ptr then begin
                let low = Option.get base_ptr in
                let chunk_size =
                  try Hashtbl.find chunk_table low
                  with Not_found -> raise (BugException (UAF, e.at, "")) in
                let high = Int64.(add (of_int32 low) (of_int32 chunk_size)) in
                let ptr_i64 = Int64.of_int32 (I32Value.of_value ptr) in
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
              let witness = Store.strings_to_json string_binds in
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
            Result.ok ([ { c with sym_code = (Value v.it) :: vs, es' } ], [])

          | Test testop, v :: vs' ->
            let es' = List.tl es in
            (try
              let v' = Static_evaluations.eval_testop v testop in
              Result.ok ([ { c with sym_code = simplify v' :: vs', es' } ], [])
            with exn ->
              Result.ok ([ { c with sym_code = vs', (STrapping (numeric_error e.at exn) @@ e.at) :: es' } ], []))

          | Compare relop, v2 :: v1 :: vs' ->
            let es' = List.tl es in
            (try
              let v = Static_evaluations.eval_relop v1 v2 relop in
              Result.ok ([ { c with sym_code = simplify v :: vs', es' } ], [])
            with exn ->
              Result.ok ([ { c with sym_code = vs', (STrapping (numeric_error e.at exn) @@ e.at) :: es' } ], []))

          | Unary unop, v :: vs' ->
            let es' = List.tl es in
            (try
              let v = Static_evaluations.eval_unop v unop in
              Result.ok ([ { c with sym_code = simplify v :: vs', es' } ], [])
            with exn ->
              Result.ok ([ { c with sym_code = vs', (STrapping (numeric_error e.at exn) @@ e.at) :: es' } ], []))

          | Binary binop, v2 :: v1 :: vs' ->
            let es' = List.tl es in
            (try
              let v = Static_evaluations.eval_binop v1 v2 binop in
              Result.ok ([ { c with sym_code = simplify v :: vs', es' } ], [])
            with exn ->
              Result.ok ([ { c with sym_code = vs', (STrapping (numeric_error e.at exn)  @@ e.at) :: es' } ], []))

          | Convert cvtop, v :: vs' ->
            let es' = List.tl es in
            (try
              let v' = Static_evaluations.eval_cvtop cvtop v in
              Result.ok ([ { c with sym_code = simplify v' :: vs', es' } ], [])
            with exn ->
              Result.ok ([ { c with sym_code = vs', (STrapping (numeric_error e.at exn)  @@ e.at) :: es' } ], []))

          | Dup, v :: vs' ->
            let vs'' = v :: v :: vs' in
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = (vs'', es') } ], [])

          | GetSymInt32 x, vs' ->
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = (Symvalue.Symbolic (SymInt32, x)) :: vs', es'} ], [])

          | GetSymInt64 x, vs' ->
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = (Symvalue.Symbolic (SymInt64, x)) :: vs', es'} ], [])

          | GetSymFloat32 x, vs' ->
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = (Symvalue.Symbolic (SymFloat32, x)) :: vs', es'} ], [])

          | GetSymFloat64 x, vs' ->
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = (Symvalue.Symbolic (SymFloat64, x)) :: vs', es'} ], [])

          | SymAssert, Value (I32 0l) :: vs' ->
            debug (string_of_pos e.at.left ^ ":Assert FAILED! Stopping...");
            let string_binds = E.string_binds encoder (Varmap.binds var_map) in
            let witness = Store.strings_to_json string_binds in
            let reason = "{" ^
            "\"type\" : \"" ^ "Assertion Failure" ^ "\", " ^
            "\"line\" : \"" ^ (string_of_pos e.at.left ^
                (if e.at.right = e.at.left then "" else "-" ^ string_of_pos e.at.right)) ^ "\"" ^
            "}"
            in
            Result.error (reason, witness)

          | SymAssert, Value (I32 i) :: vs' ->
            (* passed *)
            debug (string_of_pos e.at.left ^ ":Assert PASSED!");
            Result.ok ([ { c with sym_code = vs', List.tl es } ], [])

          | SymAssert, v :: vs' ->
            let v = simplify v in
            debug ("Asserting: " ^ Symvalue.to_string (simplify v));
            let opt_witness =
              let c = negate_relop (Option.get (to_constraint v)) in
              solver_counter := !solver_counter + 1;
              let sat = E.check encoder [ c ] in
              if sat then
                let string_binds = E.string_binds encoder (Varmap.binds var_map) in
                let witness = Store.strings_to_json string_binds in
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
            | Ptr   (I32 0l)
            | Value (I32 0l) ->
              (* if it is 0 *)
              Result.ok ([], [])
            | Ptr   (I32 _)
            | Value (I32 _) ->
              (* if it is not 0 *)
              Result.ok ([ { c with sym_code = vs, List.tl es } ], [])
            | ex -> (
              let co = Option.get (to_constraint ex) in
              solver_counter := !solver_counter + 1;
              E.add encoder co;
              if E.check encoder [] then
                let c_true = { c with sym_code = vs', List.tl es } in
                Result.ok ([ c_true ], []);
              else
                Result.ok ([], [])
              )
            )

          | Symbolic (ty, b), (Value (I32 i)) :: vs' ->
            let base = I64_convert.extend_i32_u i in
            let x = Varmap.next (SM.load_string mem base) in
            let v = to_symbolic ty x in
            let es' = List.tl es in
            Hashtbl.replace var_map x ty;
            Result.ok ([ { c with sym_code = (v :: vs', es') } ], [])

          | Boolop boolop, v1 :: v2 :: vs' ->
            (* results in i32 *)
            let v2' = mk_relop v2 I32Type in
            let v1' = mk_relop v1 I32Type in
            let v3 = Static_evaluations.eval_binop v1' v2' boolop in
            let es' = List.tl es in
            (try
              Result.ok ([ { c with sym_code = (simplify v3 :: vs', es') } ], [])
            with exn ->
              Result.ok ([ { c with sym_code = vs', (STrapping (numeric_error e.at exn) @@ e.at) :: es' } ], [])
            )

          | Alloc, Value (I32 sz) :: Value (I32 base) :: vs' ->
            Hashtbl.add chunk_table base sz;
            let sym_ptr = SymPtr (base, (Value (I32 0l))) in
            Result.ok ([{c with sym_code = sym_ptr :: vs', List.tl es}], [])

          | Alloc, s_size :: s_base :: vs' ->
            let binds = E.value_binds encoder (Varmap.binds var_map)in
            let logic_env = Store.create binds in

            let c_size = Store.eval logic_env s_size in
            let size = match c_size with
            | I32 size -> size
            | _ ->
              failwith ((Printf.sprintf "%d" e.at.left.line) ^ ":Alloc with non i32 size: " ^ Types.string_of_value_type (Values.type_of c_size));
            in
            let c_base = Store.eval logic_env s_base in
            let base = match c_base with
            | I32 base -> base
            | _ ->
              failwith ((Printf.sprintf "%d" e.at.left.line) ^ ":Alloc with non i32 base: " ^ Types.string_of_value_type (Values.type_of c_base));
            in

            let size_cond = Symvalue.I32Relop (Si32.I32Eq, s_size, Value (I32 size))
            and base_cond = Symvalue.I32Relop (Si32.I32Eq, s_base, Value (I32 base)) in

            E.add encoder size_cond;
            E.add encoder base_cond;
            Hashtbl.add chunk_table base size;

            let sym_ptr = SymPtr (base, (Value (I32 0l))) in
            (* TODO: generate a configuration equal to the original with the conditions denied in the path_cond ? *)
            Result.ok ([{ c with sym_code = sym_ptr :: vs', List.tl es }], [])

          | Free, ptr :: vs' -> (
            match simplify ptr with
            | SymPtr (base, (Value (I32 0l))) ->
              let es' =
                if not (Hashtbl.mem chunk_table base) then (
                  let string_binds = E.string_binds encoder (Varmap.binds var_map) in
                  let witness = Store.strings_to_json string_binds in
                  [Interrupt (Bug (InvalidFree, witness)) @@ e.at] @ List.tl es
                ) else (
                  Hashtbl.remove chunk_table base;
                  List.tl es
                )
              in
              Result.ok ([{c with sym_code = vs', es'}], [])
            | value ->
              failwith ("Free with invalid argument" ^ (Symvalue.pp_to_string value))
          )

          | PrintStack, vs ->
            let vs' = List.map (fun v -> (Symvalue.pp_to_string v)) vs in
            print_endline ("Stack:" ^ "\n" ^ (String.concat "\n" vs'));
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = vs, es' } ], [])

          | PrintMemory, vs ->
            print_endline ("Memory State:\n" ^ (SM.to_string mem));
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = vs, es' } ], [])

          | PrintPC, vs ->
            let open E in
            let assertion = Formula.to_formula !(encoder.pc) in
            print_endline ((Printf.sprintf "%d" e.at.left.line) ^ " pc: " ^ (Formula.pp_to_string assertion));
            let es' = List.tl es in
            Result.ok ([ { c with sym_code = vs, es' } ], [])

          | PrintValue, v:: vs' ->
            let es' = List.tl es in
            print_endline ((Printf.sprintf "%d" e.at.left.line) ^ ":val: " ^ Symvalue.pp_to_string v);
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
            let locals' = List.map (fun v -> Symvalue.Value v) (List.map default_value f.it.locals) in
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

(* TODO: make MB configurable like search and encoding *)
module LazyM_BatchE_SE = SymbolicExecutor(Encoding)(Symmem.LazySMem)
module MapM_IncrementalE_SE = SymbolicExecutor(IncrementalEncoding)(Symmem.MapSMem)
module TreeM_IncrementalE_SE = SymbolicExecutor(IncrementalEncoding)(Symmem.TreeSMem)

module HBatchSE = Strategies.Helper(LazyM_BatchE_SE)
module HIncSE = Strategies.Helper(MapM_IncrementalE_SE)
module HIncTreeSE = Strategies.Helper(TreeM_IncrementalE_SE)

let parse_encoding () =
  match !Flags.encoding with
  | "batch" -> HBatchSE.helper
  | "incremental" -> HIncSE.helper
  | "incremental-tree" -> HIncTreeSE.helper
  | _ -> failwith "unreachable"

let func_to_globs (func : func_inst): Static_globals.t =
  match Func.get_inst func with
    | (Some inst ) -> (
      let global_inst_list = (!inst).globals in
      Static_globals.from_list(global_inst_list)
    )
    | None -> Hashtbl.create 0

let invoke (func : func_inst) (vs : sym_expr list) : unit =
  let open Source in
  let at = match func with Func.AstFunc (_, _, f) -> f.at | _ -> no_region in
  let inst = try Option.get (Func.get_inst func) with Invalid_argument s ->
    Crash.error at ("sym_invoke: " ^ s) in
  (* extract globals to symbolic config *)
  let globs = func_to_globs func in
  let helper = parse_encoding () in
  let (spec, reason, witness, loop_time, solver_time, paths) = helper empty_module_inst (List.rev vs) [SInvoke func @@ at]
    !inst.sym_memory globs in

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

