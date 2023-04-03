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
  | Evaluations.UnsupportedOp m -> m ^ ": unsupported operation"
  | Interpreter.Numeric_error.IntegerOverflow -> "integer overflow"
  | Interpreter.Numeric_error.IntegerDivideByZero -> "integer divide by zero"
  | Interpreter.Numeric_error.InvalidConversionToInteger ->
      "invalid conversion to integer"
  | Interpreter.Eval_numeric.TypeError (i, v, t) ->
      Crash.error at
        ("type error, expected "
        ^ Interpreter.Types.string_of_value_type t
        ^ " as operand " ^ string_of_int i ^ ", got "
        ^ Interpreter.Types.string_of_value_type (Interpreter.Values.type_of v)
        )
  | exn -> raise exn

(* Administrative Expressions & Configurations *)
type 'a stack = 'a list

let clone_frame (frame : sym_frame) : sym_frame =
  let sym_inst = clone frame.sym_inst in
  let sym_locals = List.map (fun r -> ref !r) frame.sym_locals in
  { sym_inst; sym_locals }

(* Symbolic frame *)
let sym_frame sym_inst sym_locals = { sym_inst; sym_locals }

exception BugException of bug * Interpreter.Source.region * string

let debug str = if !Interpreter.Flags.trace then print_endline str

let time_call f args acc =
  let start = Sys.time () in
  let ret = f args in
  acc := !acc +. (Sys.time () -. start);
  ret

let plain (e : instr) : sym_admin_instr =
  let open Interpreter.Source in
  SPlain e.it @@ e.at

let lookup category list x =
  let open Interpreter.Source in
  try Interpreter.Lib.List32.nth list x.it
  with Failure _ ->
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
  try Interpreter.Lib.List.take n vs
  with Failure _ -> Crash.error at "stack underflow"

let drop n (vs : 'a stack) at =
  try Interpreter.Lib.List.drop n vs
  with Failure _ -> Crash.error at "stack underflow"

let instr_str e =
  match e with
  | Unreachable -> "unreachable"
  | Nop -> "nop"
  | Drop -> "drop"
  | Select -> "select"
  | Block (ts, es) -> "block"
  | Loop (ts, es) -> "loop"
  | If (ts, es1, es2) -> "if"
  | Br x -> "br "
  | BrIf x -> "br_if "
  | BrTable (xs, x) -> "br_table "
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

module type Encoder = sig
  type s
  type t = { solver : s; pc : Formula.t ref }

  val create : unit -> t
  val clone : t -> t
  val add : t -> expr -> unit
  val add_formula : t -> Encoding.Formula.t -> unit
  val check : t -> Expression.t option -> bool
  val fork : t -> Expression.t -> bool * bool

  val value_binds :
    t -> (string * expr_type) list -> (string * Expression.value) list

  val string_binds : t -> (string * string * string) list
end

module SymbolicInterpreter (SM : Memory.SymbolicMemory) (E : Encoder) :
  Interpreter = struct
  type sym_config = {
    sym_frame : sym_frame;
    sym_code : sym_code;
    sym_mem : SM.t;
    sym_budget : int; (* to model stack overflow *)
    varmap : Varmap.t;
    sym_globals : Globals.t;
    chunk_table : (int32, int32) Hashtbl.t;
    encoder : E.t;
  }

  type step_res = End of Formula.t | Continuation of sym_config list

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
    let vs, es = c.sym_code in
    let sym_frame = clone_frame c.sym_frame in
    let sym_code = (vs, List.map clone_admin_instr es) in
    let sm, sym_mem = SM.clone c.sym_mem in
    let sym_budget = c.sym_budget in
    let varmap = Varmap.copy c.varmap in
    let sym_globals = Globals.clone_globals c.sym_globals in
    let chunk_table = Hashtbl.copy c.chunk_table in
    let encoder = E.clone c.encoder in
    ( { c with sym_mem = sm },
      {
        sym_frame;
        sym_code;
        sym_mem;
        sym_budget;
        varmap;
        sym_globals;
        chunk_table;
        encoder;
      } )

  let sym_config (inst : module_inst) (vs : expr stack)
      (es : sym_admin_instr stack) (sym_m : Concolic.Heap.t) (globs : Globals.t)
      : sym_config =
    {
      sym_frame = sym_frame inst [];
      sym_code = (vs, es);
      sym_mem = SM.from_heap sym_m;
      (* models default recursion limit in a system *)
      sym_budget = 100000;
      varmap = Varmap.create ();
      sym_globals = globs;
      chunk_table = Hashtbl.create Interpreter.Flags.hashtbl_default_size;
      encoder = E.create ();
    }

  let to_concolic (c : sym_config) : Concolic.Eval.config =
    let open Concolic.Eval in
    let store =
      assert (E.check c.encoder None);
      let binds = E.value_binds c.encoder (Varmap.binds c.varmap) in
      Varmap.to_store c.varmap binds
    in
    let expr_to_value (ex : expr) : Num.t = Concolic.Store.eval store ex in
    let frame_to_conc (f : sym_frame) : Concolic.Eval.frame =
      let { sym_inst; sym_locals } = f in
      let locals =
        List.map
          (fun r_ex ->
            let ex = !r_ex in
            ref (expr_to_value ex, ex))
          sym_locals
      in
      { inst = sym_inst; locals }
    in
    let frame = frame_to_conc c.sym_frame in
    let glob = Globals.to_globals c.sym_globals expr_to_value in
    let vs_to_conc (vs : expr stack) : value stack =
      List.map (fun ex -> (expr_to_value ex, ex)) vs
    in
    let rec code_to_conc (code : sym_code) =
      let vs, es = code in
      let vs = vs_to_conc vs in
      let es = List.map sym_instr_to_conc es in
      (vs, es)
    and sym_instr_to_conc (instr : Strategies.sym_admin_instr) :
        Concolic.Eval.sym_admin_instr =
      let open Interpreter.Source in
      let { at; it } = instr in
      let it =
        match it with
        | Strategies.SPlain p -> Concolic.Eval.Plain p
        | Strategies.SInvoke i -> Concolic.Eval.Invoke i
        | Strategies.STrapping t -> Concolic.Eval.Trapping t
        | Strategies.SReturning vs -> Concolic.Eval.Returning (vs_to_conc vs)
        | Strategies.SBreaking (n, vs) ->
            Concolic.Eval.Breaking (n, vs_to_conc vs)
        | Strategies.SLabel (l, insts, code) ->
            Concolic.Eval.Label (l, insts, code_to_conc code)
        | Strategies.SFrame (f, frame, code) ->
            Concolic.Eval.Frame (f, frame_to_conc frame, code_to_conc code)
        | Strategies.Interrupt i -> failwith "TODO: uniform interrupts"
      in
      { at; it }
    in
    let code = code_to_conc c.sym_code in
    let mem = SM.to_heap c.sym_mem expr_to_value in
    let heap = c.chunk_table in
    let pc =
      let open E in
      !(c.encoder.pc)
    in
    let bp = [] in
    let tree = ref Concolic.Eval.head in
    let budget = c.sym_budget in
    let call_stack = Stack.create () in
    { frame; glob; code; mem; store; heap; pc; bp; tree; budget; call_stack }

  let concolic_invoke (c : sym_config) :
      (string * Interpreter.Source.region) option =
    Concolic.Eval.head := Concolic.Execution_tree.Leaf;
    debug "-- Switching to concolic mode...";
    let open E in
    debug ("-- path_condition = " ^ Formula.pp_to_string !(c.encoder.pc));
    let conc_c = to_concolic c in
    let test_suite = Filename.concat !Interpreter.Flags.output "test_suite" in
    Concolic.Eval.BFS.s_invoke conc_c test_suite

  let p_invoke (c : sym_config) :
      (Encoding.Formula.t, string * Interpreter.Source.region) result =
    let conc_c = to_concolic c
    and test_suite = Filename.concat !Interpreter.Flags.output "test_suite" in
    Concolic.Eval.BFS.p_invoke conc_c test_suite

  let p_finished (c : sym_config) (pc' : Encoding.Formula.t) : sym_config option
      =
    let npc' = Encoding.Formula.negate pc' in
    E.add_formula c.encoder npc';
    if E.check c.encoder None then Some c else None

  let memory_error at = function
    | SM.Bounds -> "out of bounds memory access"
    | Interpreter.Memory.SizeOverflow -> "memory size overflow"
    | Interpreter.Memory.SizeLimit -> "memory size limit reached"
    | Interpreter.Memory.Type -> Crash.error at "type mismatch at memory access"
    | exn -> raise exn

  let concretize_alloc (c : sym_config) : sym_config list =
    let { sym_code = vs, es; varmap; chunk_table; encoder; _ } = c in
    let e, es' =
      match es with e :: es' -> (e, es') | _ -> failwith "unreachable"
    in
    let s_size, s_base, vs' =
      match vs with
      | s_size :: s_base :: vs' -> (s_size, s_base, vs')
      | _ -> failwith "unreachable"
    in

    let helper (size : int32 option) : sym_config option =
      let size_cond =
        Option.map
          (function size -> Relop (I32 I32.Eq, s_size, Val (Num (I32 size))))
          size
      in
      match E.check encoder size_cond with
      | false -> None
      | true ->
          let _, c = clone c in
          (match size_cond with
          | Some size_cond -> E.add c.encoder size_cond
          | None -> ());
          assert (E.check c.encoder None);
          let binds = E.value_binds c.encoder (Varmap.binds c.varmap) in
          let logic_env = Concolic.Store.create binds in

          let open Interpreter.Source in
          let c_size = Concolic.Store.eval logic_env s_size in
          let size =
            match c_size with
            | I32 size -> size
            | _ ->
                failwith
                  (Printf.sprintf "%d" e.at.left.line
                  ^ ":Alloc with non i32 size: "
                  ^ Types.string_of_num_type (Types.type_of_num c_size))
          in
          let c_base = Concolic.Store.eval logic_env s_base in
          let base =
            match c_base with
            | I32 base -> base
            | _ ->
                failwith
                  (Printf.sprintf "%d" e.at.left.line
                  ^ ":Alloc with non i32 base: "
                  ^ Types.string_of_num_type (Types.type_of_num c_base))
          in

          let base_cond = Relop (I32 I32.Eq, s_base, Val (Num (I32 base))) in
          E.add c.encoder base_cond;
          Hashtbl.add c.chunk_table base size;

          let sym_ptr = SymPtr (base, Val (Num (I32 0l))) in
          Some { c with sym_code = (sym_ptr :: List.tl vs, List.tl es) }
    in

    let fixed_attempts =
      List.filter_map helper
        (List.map Option.some
           (List.map Int32.of_int !Interpreter.Flags.fixed_numbers))
    in
    if List.length fixed_attempts > 0 then fixed_attempts
    else [ Option.get (helper None) ]

  let rec step (c : sym_config) :
      (step_res, string * Interpreter.Source.region) result =
    let {
      sym_frame = frame;
      sym_code = vs, es;
      sym_mem = mem;
      varmap;
      chunk_table;
      encoder;
      _;
    } =
      c
    in
    let open Interpreter in
    let open Source in
    match es with
    | [] ->
        assert (E.check encoder None);
        let string_binds = E.string_binds encoder in
        let witness = Concolic.Store.strings_to_json string_binds in
        Concolic.Eval.write_test_case witness;
        let open E in
        Result.ok (End !(encoder.pc))
    | e :: t -> (
        match (e.it, vs) with
        | SPlain e', vs -> (
            match (e', vs) with
            | Nop, vs ->
                Result.ok
                  (Continuation [ { c with sym_code = (vs, List.tl es) } ])
            | Drop, v :: vs' ->
                Result.ok
                  (Continuation [ { c with sym_code = (vs', List.tl es) } ])
            | Select, ex :: v2 :: v1 :: vs' -> (
                match simplify ex with
                | Val (Num (I32 0l)) ->
                    (* if it is 0 *)
                    Result.ok
                      (Continuation
                         [ { c with sym_code = (v2 :: vs', List.tl es) } ])
                | Val (Num (I32 _)) ->
                    (* if it is not 0 *)
                    Result.ok
                      (Continuation
                         [ { c with sym_code = (v1 :: vs', List.tl es) } ])
                | ex ->
                    let co = Option.get (to_relop ex) in
                    let negated_co = negate_relop co in
                    let es' = List.tl es in

                    let sat_then, sat_else = E.fork encoder co in

                    let l =
                      match (sat_then, sat_else) with
                      | true, true ->
                          let c, c_clone = clone c in
                          E.add c.encoder co;
                          E.add c_clone.encoder negated_co;
                          [
                            { c with sym_code = (v1 :: vs', es') };
                            { c_clone with sym_code = (v2 :: vs', es') };
                          ]
                      | true, false ->
                          E.add encoder co;
                          [ { c with sym_code = (v1 :: vs', es') } ]
                      | false, true ->
                          E.add encoder negated_co;
                          [ { c with sym_code = (v2 :: vs', es') } ]
                      | false, false -> failwith "Unreachable Select"
                    in

                    Result.ok (Continuation l))
            | Block (ts, es'), vs ->
                let es0 =
                  SLabel (List.length ts, [], ([], List.map plain es')) @@ e.at
                in
                Result.ok
                  (Continuation
                     [ { c with sym_code = (vs, es0 :: List.tl es) } ])
            | Loop (ts, es'), vs ->
                let es0 =
                  SLabel (0, [ e' @@ e.at ], ([], List.map plain es')) @@ e.at
                in
                Result.ok
                  (Continuation
                     [ { c with sym_code = (vs, es0 :: List.tl es) } ])
            | If (ts, es1, es2), ex :: vs' -> (
                let es' = List.tl es in
                match simplify ex with
                | Val (Num (I32 0l)) ->
                    (* if it is 0 *)
                    Result.ok
                      (Continuation
                         [
                           {
                             c with
                             sym_code =
                               (vs', [ SPlain (Block (ts, es2)) @@ e.at ] @ es');
                           };
                         ])
                | Val (Num (I32 _)) ->
                    (* if it is not 0 *)
                    Result.ok
                      (Continuation
                         [
                           {
                             c with
                             sym_code =
                               (vs', [ SPlain (Block (ts, es1)) @@ e.at ] @ es');
                           };
                         ])
                | ex ->
                    let co = Option.get (to_relop ex) in
                    let negated_co = negate_relop co in

                    let sat_then, sat_else = E.fork encoder co in

                    let l =
                      match (sat_then, sat_else) with
                      | true, true ->
                          let c, c_clone = clone c in
                          E.add c.encoder co;
                          E.add c_clone.encoder negated_co;
                          [
                            {
                              c with
                              sym_code =
                                (vs', [ SPlain (Block (ts, es1)) @@ e.at ] @ es');
                            };
                            {
                              c_clone with
                              sym_code =
                                (vs', [ SPlain (Block (ts, es2)) @@ e.at ] @ es');
                            };
                          ]
                      | true, false ->
                          E.add encoder co;
                          [
                            {
                              c with
                              sym_code =
                                (vs', [ SPlain (Block (ts, es1)) @@ e.at ] @ es');
                            };
                          ]
                      | false, true ->
                          E.add encoder negated_co;
                          [
                            {
                              c with
                              sym_code =
                                (vs', [ SPlain (Block (ts, es2)) @@ e.at ] @ es');
                            };
                          ]
                      | false, false -> failwith "Unreachable If"
                    in

                    Result.ok (Continuation l))
            | Br x, vs ->
                Result.ok
                  (Continuation
                     [
                       {
                         c with
                         sym_code = (vs, [ SBreaking (x.it, vs) @@ e.at ]);
                       };
                     ])
            | BrIf x, ex :: vs' -> (
                match simplify ex with
                | Val (Num (I32 0l)) ->
                    (* if it is 0 *)
                    let es' = List.tl es in
                    Result.ok
                      (Continuation [ { c with sym_code = (vs', es') } ])
                | Val (Num (I32 _)) ->
                    (* if it is not 0 *)
                    Result.ok
                      (Continuation
                         [
                           {
                             c with
                             sym_code = (vs', [ SPlain (Br x) @@ e.at ]);
                           };
                         ])
                | ex ->
                    let co = Option.get (to_relop ex) in
                    let negated_co = negate_relop co in
                    let es' = List.tl es in

                    let sat_then, sat_else = E.fork encoder co in

                    let l =
                      match (sat_then, sat_else) with
                      | true, true ->
                          let c, c_clone = clone c in
                          E.add c.encoder co;
                          E.add c_clone.encoder negated_co;
                          [
                            {
                              c with
                              sym_code = (vs', [ SPlain (Br x) @@ e.at ]);
                            };
                            { c_clone with sym_code = (vs', es') };
                          ]
                      | true, false ->
                          E.add encoder co;
                          [
                            {
                              c with
                              sym_code = (vs', [ SPlain (Br x) @@ e.at ]);
                            };
                          ]
                      | false, true ->
                          E.add encoder negated_co;
                          [ { c with sym_code = (vs', es') } ]
                      | false, false -> failwith "Unreachable BrIf"
                    in

                    Result.ok (Continuation l))
            | Return, vs ->
                let es' = [ SReturning vs @@ e.at ] @ List.tl es in
                Result.ok (Continuation [ { c with sym_code = ([], es') } ])
            | Call x, vs ->
                Result.ok
                  (Continuation
                     [
                       {
                         c with
                         sym_code =
                           (vs, [ SInvoke (func frame.sym_inst x) @@ e.at ] @ t);
                       };
                     ])
            | CallIndirect x, Val (Num (I32 i)) :: vs ->
                let func = func_elem frame.sym_inst (0l @@ e.at) i e.at in
                let es' =
                  if type_ frame.sym_inst x <> Func.type_of func then
                    [ STrapping "indirect call type mismatch" @@ e.at ]
                  else [ SInvoke func @@ e.at ]
                in
                Result.ok
                  (Continuation [ { c with sym_code = (vs, es' @ List.tl es) } ])
            | LocalGet x, vs ->
                let vs' = !(local frame x) :: vs in
                let es' = List.tl es in
                Result.ok (Continuation [ { c with sym_code = (vs', es') } ])
            | LocalSet x, v :: vs' ->
                local frame x := v;
                let es' = List.tl es in
                Result.ok (Continuation [ { c with sym_code = (vs', es') } ])
            | LocalTee x, v :: vs' ->
                local frame x := v;
                let es' = List.tl es in
                Result.ok
                  (Continuation [ { c with sym_code = (v :: vs', es') } ])
            | GlobalGet x, vs ->
                let v' = Globals.load c.sym_globals x.it in
                let es' = List.tl es in
                Result.ok
                  (Continuation [ { c with sym_code = (v' :: vs, es') } ])
            | GlobalSet x, v :: vs' -> (
                let es' = List.tl es in
                try
                  Globals.store c.sym_globals x.it v;
                  Result.ok (Continuation [ { c with sym_code = (vs', es') } ])
                with
                | Global.NotMutable ->
                    Crash.error e.at "write to immutable global"
                | Global.Type ->
                    Crash.error e.at "type mismatch at global write")
            | Load { offset; ty; sz; _ }, sym_ptr :: vs' -> (
                let sym_ptr = simplify sym_ptr in
                let ptr =
                  match concretize_ptr sym_ptr with
                  | Some ptr -> ptr
                  | None ->
                      assert (E.check encoder None);
                      let binds = E.value_binds encoder (Varmap.binds varmap) in
                      let logic_env = Concolic.Store.create binds in

                      let ptr = Concolic.Store.eval logic_env sym_ptr in
                      let ty = Encoding.Types.type_of_num ptr in
                      if ty != `I32Type then
                        failwith
                          (Printf.sprintf "%d" e.at.left.line
                          ^ ":Load with non i32 ptr: "
                          ^ Encoding.Types.string_of_num_type ty);

                      let ptr_cond =
                        Relop (I32 Encoding.Types.I32.Eq, sym_ptr, Val (Num ptr))
                      in
                      E.add encoder ptr_cond;

                      (* TODO: generate a configuration equal to the original with the condition denied in the path_cond ? *)
                      ptr
                in
                let ptr64 =
                  I64_convert.extend_i32_u
                    (Values.I32Value.of_value (Evaluations.to_value ptr))
                in
                let base_ptr = concretize_base_ptr sym_ptr in
                try
                  (if Option.is_some base_ptr then
                   let low = Option.get base_ptr in
                   let chunk_size =
                     try Hashtbl.find chunk_table low
                     with Not_found -> raise (BugException (UAF, e.at, ""))
                   in
                   let high =
                     Int64.(add (of_int32 low) (of_int32 chunk_size))
                   in
                   let ptr_i64 =
                     Int64.of_int32
                       (Values.I32Value.of_value (Evaluations.to_value ptr))
                   in
                   let ptr_val = Int64.(add ptr_i64 (of_int32 offset)) in
                   (* ptr_val \notin [low, high] => overflow *)
                   if ptr_val < Int64.of_int32 low || ptr_val >= high then
                     raise (BugException (Overflow, e.at, "")));
                  let v =
                    match sz with
                    | None ->
                        SM.load_value mem ptr64 offset
                          (Evaluations.to_num_type ty)
                    | Some (sz, _) ->
                        SM.load_packed sz mem ptr64 offset
                          (Evaluations.to_num_type ty)
                  in
                  let es' = List.tl es in
                  Result.ok
                    (Continuation [ { c with sym_code = (v :: vs', es') } ])
                with
                | BugException (b, at, _) ->
                    assert (E.check encoder None);
                    let string_binds = E.string_binds encoder in
                    let witness = Concolic.Store.strings_to_json string_binds in
                    Concolic.Eval.write_test_case ~witness:true witness;
                    let bug_type =
                      match b with
                      | Overflow -> "Out of Bounds access"
                      | UAF -> "Use After Free"
                      | _ ->
                          failwith "unreachable, other bugs shouldn't be here"
                    in
                    Result.error (bug_type, at)
                | exn ->
                    Result.ok
                      (Continuation
                         [
                           {
                             c with
                             sym_code =
                               ( vs',
                                 [ STrapping (memory_error e.at exn) @@ e.at ]
                               );
                           };
                         ]))
            | Store { offset; sz; _ }, ex :: sym_ptr :: vs' -> (
                let sym_ptr = simplify sym_ptr in
                let ptr =
                  match concretize_ptr sym_ptr with
                  | Some ptr -> ptr
                  | None ->
                      assert (E.check encoder None);
                      let binds = E.value_binds encoder (Varmap.binds varmap) in
                      let logic_env = Concolic.Store.create binds in

                      let ptr = Concolic.Store.eval logic_env sym_ptr in
                      let ty = Encoding.Types.type_of_num ptr in
                      if ty != `I32Type then
                        failwith
                          (Printf.sprintf "%d" e.at.left.line
                          ^ ":Store with non i32 ptr: "
                          ^ Encoding.Types.string_of_num_type ty);

                      let ptr_cond =
                        Relop (I32 Encoding.Types.I32.Eq, sym_ptr, Val (Num ptr))
                      in
                      E.add encoder ptr_cond;

                      (* TODO: generate a configuration equal to the original with the condition denied in the path_cond ? *)
                      ptr
                in
                let ptr64 =
                  I64_convert.extend_i32_u
                    (Values.I32Value.of_value (Evaluations.to_value ptr))
                in
                let base_ptr = concretize_base_ptr sym_ptr in
                try
                  (if Option.is_some base_ptr then
                   let low = Option.get base_ptr in
                   let chunk_size =
                     try Hashtbl.find chunk_table low
                     with Not_found -> raise (BugException (UAF, e.at, ""))
                   in
                   let high =
                     Int64.(add (of_int32 low) (of_int32 chunk_size))
                   in
                   let ptr_i64 =
                     Int64.of_int32
                       (Values.I32Value.of_value (Evaluations.to_value ptr))
                   in
                   let ptr_val = Int64.(add ptr_i64 (of_int32 offset)) in
                   (* ptr_val \notin [low, high[ => overflow *)
                   if ptr_val < Int64.of_int32 low || ptr_val >= high then
                     raise (BugException (Overflow, e.at, "")));
                  (match sz with
                  | None -> SM.store_value mem ptr64 offset ex
                  | Some sz -> SM.store_packed sz mem ptr64 offset ex);
                  let es' = List.tl es in
                  Result.ok (Continuation [ { c with sym_code = (vs', es') } ])
                with
                | BugException (b, at, _) ->
                    assert (E.check encoder None);
                    let string_binds = E.string_binds encoder in
                    let witness = Concolic.Store.strings_to_json string_binds in
                    Concolic.Eval.write_test_case ~witness:true witness;
                    let bug_type =
                      match b with
                      | Overflow -> "Out of Bounds access"
                      | UAF -> "Use After Free"
                      | _ ->
                          failwith "unreachable, other bugs shouldn't be here"
                    in
                    Result.error (bug_type, at)
                | exn ->
                    Result.ok
                      (Continuation
                         [
                           {
                             c with
                             sym_code =
                               ( vs',
                                 [ STrapping (memory_error e.at exn) @@ e.at ]
                               );
                           };
                         ]))
            | Const v, vs ->
                let es' = List.tl es in
                Result.ok
                  (Continuation
                     [
                       {
                         c with
                         sym_code =
                           (Val (Num (Evaluations.of_value v.it)) :: vs, es');
                       };
                     ])
            | Test testop, v :: vs' -> (
                let es' = List.tl es in
                try
                  let v' = Evaluations.eval_testop v testop in
                  Result.ok
                    (Continuation
                       [ { c with sym_code = (simplify v' :: vs', es') } ])
                with exn ->
                  Result.ok
                    (Continuation
                       [
                         {
                           c with
                           sym_code =
                             ( vs',
                               (STrapping (numeric_error e.at exn) @@ e.at)
                               :: es' );
                         };
                       ]))
            | Compare relop, v2 :: v1 :: vs' -> (
                let es' = List.tl es in
                try
                  let v = Evaluations.eval_relop v1 v2 relop in
                  Result.ok
                    (Continuation
                       [ { c with sym_code = (simplify v :: vs', es') } ])
                with exn ->
                  Result.ok
                    (Continuation
                       [
                         {
                           c with
                           sym_code =
                             ( vs',
                               (STrapping (numeric_error e.at exn) @@ e.at)
                               :: es' );
                         };
                       ]))
            | Unary unop, v :: vs' -> (
                let es' = List.tl es in
                try
                  let v = Evaluations.eval_unop v unop in
                  Result.ok
                    (Continuation
                       [ { c with sym_code = (simplify v :: vs', es') } ])
                with exn ->
                  Result.ok
                    (Continuation
                       [
                         {
                           c with
                           sym_code =
                             ( vs',
                               (STrapping (numeric_error e.at exn) @@ e.at)
                               :: es' );
                         };
                       ]))
            | Binary binop, v2 :: v1 :: vs' -> (
                let es' = List.tl es in
                try
                  let v = Evaluations.eval_binop v1 v2 binop in
                  Result.ok
                    (Continuation
                       [ { c with sym_code = (simplify v :: vs', es') } ])
                with exn ->
                  Result.ok
                    (Continuation
                       [
                         {
                           c with
                           sym_code =
                             ( vs',
                               (STrapping (numeric_error e.at exn) @@ e.at)
                               :: es' );
                         };
                       ]))
            | Convert cvtop, v :: vs' -> (
                let es' = List.tl es in
                try
                  let v' = Evaluations.eval_cvtop cvtop v in
                  Result.ok
                    (Continuation
                       [ { c with sym_code = (simplify v' :: vs', es') } ])
                with exn ->
                  Result.ok
                    (Continuation
                       [
                         {
                           c with
                           sym_code =
                             ( vs',
                               (STrapping (numeric_error e.at exn) @@ e.at)
                               :: es' );
                         };
                       ]))
            | Dup, v :: vs' ->
                let vs'' = v :: v :: vs' in
                let es' = List.tl es in
                Result.ok (Continuation [ { c with sym_code = (vs'', es') } ])
            | GetSymInt32 x, vs' ->
                let es' = List.tl es in
                Result.ok
                  (Continuation
                     [
                       {
                         c with
                         sym_code = (Symbolic (`I32Type, x) :: vs', es');
                       };
                     ])
            | GetSymInt64 x, vs' ->
                let es' = List.tl es in
                Result.ok
                  (Continuation
                     [
                       {
                         c with
                         sym_code = (Symbolic (`I64Type, x) :: vs', es');
                       };
                     ])
            | GetSymFloat32 x, vs' ->
                let es' = List.tl es in
                Result.ok
                  (Continuation
                     [
                       {
                         c with
                         sym_code = (Symbolic (`F32Type, x) :: vs', es');
                       };
                     ])
            | GetSymFloat64 x, vs' ->
                let es' = List.tl es in
                Result.ok
                  (Continuation
                     [
                       {
                         c with
                         sym_code = (Symbolic (`F64Type, x) :: vs', es');
                       };
                     ])
            | SymAssert, Val (Num (I32 0l)) :: vs' ->
                debug (string_of_pos e.at.left ^ ":Assert FAILED! Stopping...");
                assert (E.check encoder None);
                let string_binds = E.string_binds encoder in
                let witness = Concolic.Store.strings_to_json string_binds in
                Concolic.Eval.write_test_case ~witness:true witness;
                Result.error ("Assertion Failure", e.at)
            | SymAssert, Val (Num (I32 i)) :: vs' ->
                (* passed *)
                debug (string_of_pos e.at.left ^ ":Assert PASSED!");
                Result.ok
                  (Continuation [ { c with sym_code = (vs', List.tl es) } ])
            | SymAssert, v :: vs' ->
                let v = simplify v in
                debug ("Asserting: " ^ Expression.to_string (simplify v));
                let constr = negate_relop (Option.get (to_relop v)) in
                let sat = E.check encoder (Some constr) in
                if sat then (
                  E.add encoder constr;
                  assert (E.check encoder None);
                  let string_binds = E.string_binds encoder in
                  let witness = Concolic.Store.strings_to_json string_binds in
                  debug (string_of_pos e.at.left ^ ":Assert FAILED! Stopping...");
                  Concolic.Eval.write_test_case ~witness:true witness;
                  Result.error ("Assertion Failure", e.at))
                else (
                  debug (string_of_pos e.at.left ^ ":Assert PASSED!");
                  Result.ok
                    (Continuation [ { c with sym_code = (vs', List.tl es) } ]))
            | SymAssume, ex :: vs' -> (
                match simplify ex with
                | Val (Num (I32 0l)) ->
                    (* if it is 0 *)
                    Result.ok (Continuation [])
                | SymPtr (_, Val (Num (I32 0l))) | Val (Num (I32 _)) ->
                    (* if it is not 0 *)
                    Result.ok
                      (Continuation [ { c with sym_code = (vs, List.tl es) } ])
                | ex ->
                    let co = Option.get (to_relop ex) in
                    E.add encoder co;
                    if E.check encoder None then
                      let c_true = { c with sym_code = (vs', List.tl es) } in
                      Result.ok (Continuation [ c_true ])
                    else Result.ok (Continuation []))
            | Symbolic (ty, b), Val (Num (I32 i)) :: vs' ->
                let base = I64_convert.extend_i32_u i in
                let symbol = if i = 0l then "x" else SM.load_string mem base in
                let x = Varmap.next varmap symbol in
                let ty' = Evaluations.to_num_type ty in
                let v = symbolic ty' x in
                let es' = List.tl es in
                Varmap.add varmap x ty';
                Result.ok
                  (Continuation [ { c with sym_code = (v :: vs', es') } ])
            | Boolop boolop, v1 :: v2 :: vs' -> (
                (* results in i32 *)
                let v2' = mk_relop v2 `I32Type in
                let v1' = mk_relop v1 `I32Type in
                let v3 = Evaluations.eval_binop v1' v2' boolop in
                let es' = List.tl es in
                try
                  Result.ok
                    (Continuation
                       [ { c with sym_code = (simplify v3 :: vs', es') } ])
                with exn ->
                  Result.ok
                    (Continuation
                       [
                         {
                           c with
                           sym_code =
                             ( vs',
                               (STrapping (numeric_error e.at exn) @@ e.at)
                               :: es' );
                         };
                       ]))
            | Alloc, Val (Num (I32 sz)) :: Val (Num (I32 base)) :: vs' ->
                Hashtbl.add chunk_table base sz;
                let sym_ptr = SymPtr (base, Val (Num (I32 0l))) in
                Result.ok
                  (Continuation
                     [ { c with sym_code = (sym_ptr :: vs', List.tl es) } ])
            | Alloc, _ :: _ :: vs' ->
                Result.ok (Continuation (concretize_alloc c))
            | Free, ptr :: vs' -> (
                match simplify ptr with
                | SymPtr (base, Val (Num (I32 0l))) ->
                    let es' =
                      if not (Hashtbl.mem chunk_table base) then (
                        assert (E.check encoder None);
                        let string_binds = E.string_binds encoder in
                        let witness =
                          Concolic.Store.strings_to_json string_binds
                        in
                        [ Interrupt (Bug (InvalidFree, witness)) @@ e.at ]
                        @ List.tl es)
                      else (
                        Hashtbl.remove chunk_table base;
                        List.tl es)
                    in
                    Result.ok
                      (Continuation [ { c with sym_code = (vs', es') } ])
                | value ->
                    failwith ("Free with invalid argument" ^ pp_to_string value)
                )
            | PrintStack, vs ->
                let vs' = List.map (fun v -> Expression.pp_to_string v) vs in
                debug
                  ("Stack @ "
                  ^ Source.string_of_pos e.at.left
                  ^ ":" ^ "\n" ^ String.concat "\n" vs');
                let es' = List.tl es in
                Result.ok (Continuation [ { c with sym_code = (vs, es') } ])
            | PrintMemory, vs ->
                print_endline ("Memory State:\n" ^ SM.to_string mem);
                let es' = List.tl es in
                Result.ok (Continuation [ { c with sym_code = (vs, es') } ])
            | PrintPC, vs ->
                let open E in
                print_endline
                  (Printf.sprintf "%d" e.at.left.line
                  ^ " pc: "
                  ^ Encoding.Formula.pp_to_string !(encoder.pc));
                let es' = List.tl es in
                Result.ok (Continuation [ { c with sym_code = (vs, es') } ])
            | PrintValue, v :: vs' ->
                let es' = List.tl es in
                print_endline
                  (Printf.sprintf "%d" e.at.left.line
                  ^ ":val: " ^ Expression.pp_to_string v);
                Result.ok (Continuation [ { c with sym_code = (vs, es') } ])
            | _ ->
                print_endline
                  (string_of_region e.at ^ ":Not implemented " ^ instr_str e');
                let reason =
                  "{" ^ "\"type\" : \"" ^ "Not implemented" ^ "\", "
                  ^ "\"line\" : \""
                  ^ (string_of_pos e.at.left
                    ^
                    if e.at.right = e.at.left then ""
                    else "-" ^ string_of_pos e.at.right)
                  ^ "\"" ^ "}"
                in
                Result.error (reason, e.at))
        | SLabel (n, es0, (vs', [])), vs ->
            Result.ok
              (Continuation [ { c with sym_code = (vs' @ vs, List.tl es) } ])
        | SLabel (n, es0, (vs', { it = Interrupt i; at } :: es')), vs ->
            let es' =
              (Interrupt i @@ at) :: [ SLabel (n, es0, (vs', es')) @@ e.at ]
            in
            Result.ok
              (Continuation [ { c with sym_code = (vs, es' @ List.tl es) } ])
        | SLabel (n, es0, (vs', { it = STrapping msg; at } :: es')), vs ->
            (* TODO *)
            Trap.error e.at "trap"
        | SLabel (n, es0, (vs', { it = SReturning vs0; at } :: es')), vs ->
            let vs'' = take n vs0 e.at @ vs in
            Result.ok
              (Continuation [ { c with sym_code = (vs'', List.tl es) } ])
        | SLabel (n, es0, (vs', { it = SBreaking (0l, vs0); at } :: es')), vs ->
            let vs'' = take n vs0 e.at @ vs in
            let es' = List.map plain es0 in
            Result.ok
              (Continuation [ { c with sym_code = (vs'', es' @ List.tl es) } ])
        | SLabel (n, es0, (vs', { it = SBreaking (k, vs0); at } :: es')), vs ->
            let es0' = SBreaking (Int32.sub k 1l, vs0) @@ at in
            Result.ok
              (Continuation [ { c with sym_code = (vs, es0' :: List.tl es) } ])
        | SLabel (n, es0, code'), vs ->
            Result.map
              (fun step_r ->
                match step_r with
                | End pc -> End pc
                | Continuation cs ->
                    Continuation
                      (List.map
                         (fun (c' : sym_config) ->
                           let es0' = SLabel (n, es0, c'.sym_code) @@ e.at in
                           { c' with sym_code = (vs, es0' :: List.tl es) })
                         cs))
              (step { c with sym_code = code' })
        | SFrame (n, frame', (vs', [])), vs ->
            Result.ok
              (Continuation [ { c with sym_code = (vs' @ vs, List.tl es) } ])
        | SFrame (n, frame', (vs', { it = Interrupt i; at } :: es')), vs ->
            let es' =
              (Interrupt i @@ at) :: [ SFrame (n, frame', (vs', es')) @@ e.at ]
            in
            Result.ok
              (Continuation [ { c with sym_code = (vs, es' @ List.tl es) } ])
        | SFrame (n, frame', (vs', { it = STrapping msg; at } :: es')), vs ->
            (* TODO *)
            Trap.error e.at "trap"
        | SFrame (n, frame', (vs', { it = SReturning vs0; at } :: es')), vs ->
            let vs'' = take n vs0 e.at @ vs in
            Result.ok
              (Continuation [ { c with sym_code = (vs'', List.tl es) } ])
        | SFrame (n, frame', code'), vs ->
            Result.map
              (fun step_r ->
                match step_r with
                | End pc -> End pc
                | Continuation cs ->
                    Continuation
                      (List.map
                         (fun (c' : sym_config) ->
                           let es0 =
                             SFrame (n, c'.sym_frame, c'.sym_code) @@ e.at
                           in
                           {
                             c' with
                             sym_code = (vs, es0 :: List.tl es);
                             sym_frame = clone_frame frame;
                           })
                         cs))
              (step
                 {
                   sym_frame = frame';
                   sym_code = code';
                   sym_mem = c.sym_mem;
                   sym_budget = c.sym_budget - 1;
                   varmap = c.varmap;
                   sym_globals = c.sym_globals;
                   chunk_table = c.chunk_table;
                   encoder = c.encoder;
                 })
        | STrapping msg, vs -> assert false
        | Interrupt i, vs -> assert false
        | SReturning vs', vs -> Crash.error e.at "undefined frame"
        | SBreaking (k, vs'), vs -> Crash.error e.at "undefined label"
        | SInvoke func, vs when c.sym_budget = 0 ->
            (* stop execution if call stack is too deep *)
            Result.ok (Continuation [])
        | SInvoke func, vs -> (
            let (FuncType (ins, out)) = Func.type_of func in
            let n = List.length ins in
            let args, vs' = (take n vs e.at, drop n vs e.at) in
            match func with
            | Func.AstFunc (t, inst', f) ->
                let locals' =
                  List.map
                    (fun v -> Val (Num v))
                    (List.map
                       (fun t -> Num.default_value (Evaluations.to_num_type t))
                       f.it.locals)
                in
                let locals'' = List.rev args @ locals' in
                let code' = ([], [ SPlain (Block (out, f.it.body)) @@ f.at ]) in
                let frame' =
                  { sym_inst = !inst'; sym_locals = List.map ref locals'' }
                in
                let es0 = SFrame (List.length out, frame', code') @@ e.at in
                Result.ok
                  (Continuation
                     [ { c with sym_code = (vs', es0 :: List.tl es) } ])
            | Func.HostFunc (t, f) -> failwith "HostFunc error"))
end

module EncodingSelector (SM : Memory.SymbolicMemory) = struct
  module SI_SM = SymbolicInterpreter (SM)
  module BatchHelper = Strategies.Helper (SI_SM (Encoding.Batch))
  module IncrementalHelper = Strategies.Helper (SI_SM (Encoding.Incremental))

  let parse_encoding () =
    match !Interpreter.Flags.encoding with
    | "batch" -> BatchHelper.helper
    | "incremental" -> IncrementalHelper.helper
    | _ -> failwith "Invalid encoding option"
end

module MapMem_EncondingSelector = EncodingSelector (Memory.MapSMem)
module LazyMem_EncondingSelector = EncodingSelector (Memory.LazySMem)
module TreeMem_EncondingSelector = EncodingSelector (Memory.TreeSMem)

let parse_memory_and_encoding () =
  match !Interpreter.Flags.memory with
  | "map" -> MapMem_EncondingSelector.parse_encoding ()
  | "lazy" -> LazyMem_EncondingSelector.parse_encoding ()
  | "tree" -> TreeMem_EncondingSelector.parse_encoding ()
  | _ -> failwith "Invalid memory backend"

let func_to_globs (func : func_inst) : Globals.t =
  match Interpreter.Func.get_inst func with
  | Some inst -> Globals.from_list !inst.globals
  | None -> Hashtbl.create 0

let write_report (error : (string * Interpreter.Source.region) option)
    (loop_time : float) (paths : int) (step_count : int) : unit =
  let spec, reason =
    match error with
    | None -> (true, "{}")
    | Some e -> (false, Concolic.Eval.get_reason e)
  in
  let solver_time =
    !Encoding.Incremental.solver_time +. !Encoding.Batch.solver_time
  in
  let solver_count =
    !Encoding.Incremental.solver_count + !Encoding.Batch.solver_count
  in
  let report_str =
    "{" ^ "\"specification\": " ^ string_of_bool spec ^ ", " ^ "\"reason\" : "
    ^ reason ^ ", " ^ "\"loop_time\" : \"" ^ string_of_float loop_time ^ "\", "
    ^ "\"solver_time\" : \""
    ^ string_of_float solver_time
    ^ "\", " ^ "\"paths_explored\" : " ^ string_of_int paths ^ ", "
    ^ "\"solver_counter\" : " ^ string_of_int solver_count ^ ", "
    ^ "\"instruction_counter\" : " ^ string_of_int step_count ^ "}"
  in
  Interpreter.Io.save_file
    (Filename.concat !Interpreter.Flags.output "report.json")
    report_str

let invoke (func : func_inst) (vs : expr list) (mem0 : Concolic.Heap.t) =
  let open Interpreter.Source in
  let at =
    match func with
    | Interpreter.Func.AstFunc (_, _, f) -> f.at
    | _ -> no_region
  in
  (* extract globals to symbolic config *)
  let globs = func_to_globs func in
  let helper = parse_memory_and_encoding () in

  Interpreter.Io.safe_mkdir !Interpreter.Flags.output;
  let test_suite = Filename.concat !Interpreter.Flags.output "test_suite" in
  Interpreter.Io.safe_mkdir test_suite;

  let spec, reason, loop_time, paths =
    helper empty_module_inst (List.rev vs) [ SInvoke func @@ at ] mem0 globs
  in

  (* TODO: review solver_counter, hybrid will be wrong *)
  write_report reason loop_time paths 0
