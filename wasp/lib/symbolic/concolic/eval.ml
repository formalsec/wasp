open Common
open Encoding
open Expression
open Evaluations
open Types
open Interpreter.Ast
open Interpreter.Source
open Interpreter.Instance
module Link = Interpreter.Error.Make ()
module Trap = Interpreter.Error.Make ()
module Crash = Interpreter.Error.Make ()
module Exhaustion = Interpreter.Error.Make ()

exception Link = Link.Error
exception Trap = Trap.Error
exception Crash = Crash.Error
exception Exhaustion = Exhaustion.Error

let memory_error at = function
  | Heap.InvalidAddress a ->
      Int64.to_string a ^ ":address not found in hashtable"
  | Heap.Bounds -> "out of bounds memory access"
  | Interpreter.Memory.SizeOverflow -> "memory size overflow"
  | Interpreter.Memory.SizeLimit -> "memory size limit reached"
  | Interpreter.Memory.Type -> Crash.error at "type mismatch at memory access"
  | exn -> raise exn

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

type policy = Random | Depth | Breadth
type bug = Overflow | UAF | InvalidFree
type interruption = Limit | Failure of pc | Bug of bug
type 'a stack = 'a list
type frame = { inst : module_inst; locals : value ref list }

type code = value stack * sym_admin_instr list
and sym_admin_instr = sym_admin_instr' phrase

and sym_admin_instr' =
  | Plain of instr'
  | Invoke of func_inst
  | Trapping of string
  | Returning of value stack
  | Breaking of int32 * value stack
  | Label of int * instr list * code
  | Frame of int * frame * code
  | Interrupt of interruption
  | Restart of pc

type config = {
  frame : frame;
  glob : Globals.t;
  code : code;
  mem : Heap.t;
  store : Store.t;
  heap : (int32, int32) Hashtbl.t;
  pc : pc;
  bp : pc list;
  tree : Execution_tree.t ref ref;
  budget : int;
}

let frame inst locals = { inst; locals }

let config inst vs es mem glob tree =
  {
    frame = frame inst [];
    glob;
    code = (vs, es);
    mem;
    store = Store.create [];
    heap = Hashtbl.create Interpreter.Flags.hashtbl_default_size;
    pc = [];
    bp = [];
    tree;
    budget = 100000;
  }

exception BugException of config * region * bug

let head = ref Execution_tree.Leaf
let step_cnt = ref 0
let solver_cnt = ref 0
let iterations = ref 0
let solver_time = ref 0.
let loop_start = ref 0.
let solver = Encoding.Batch.create ()
let debug str = if !Interpreter.Flags.trace then print_endline str

let count (init : int) : unit -> int =
  let next = ref init in
  let next () =
    let n = !next in
    next := n + 1;
    n
  in
  next

let parse_policy (p : string) : policy option =
  match p with
  | "random" -> Some Random
  | "depth" -> Some Depth
  | "breadth" -> Some Breadth
  | _ -> None

let string_of_bug : bug -> string = function
  | Overflow -> "Overflow"
  | UAF -> "Use After Free"
  | InvalidFree -> "Invalid Free"

let string_of_interruption : interruption -> string = function
  | Limit -> "Instruction Limit"
  | Failure _ -> "Assertion Failure"
  | Bug b -> string_of_bug b

let plain e = Plain e.it @@ e.at

let lookup category list x =
  try Interpreter.Lib.List32.nth list x.it
  with Failure _ ->
    Crash.error x.at ("undefined " ^ category ^ " " ^ Int32.to_string x.it)

let type_ (inst : module_inst) x = lookup "type" inst.types x
let func (inst : module_inst) x = lookup "function" inst.funcs x
let table (inst : module_inst) x = lookup "table" inst.tables x
let memory (inst : module_inst) x = lookup "memory" inst.memories x
let global (inst : module_inst) x = lookup "global" inst.globals x
let local (frame : frame) x = lookup "local" frame.locals x

let elem inst x i at =
  match Interpreter.Table.load (table inst x) i with
  | Interpreter.Table.Uninitialized ->
      Trap.error at ("uninitialized element " ^ Int32.to_string i)
  | f -> f
  | exception Interpreter.Table.Bounds ->
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

let branch_on_cond bval c pc tree =
  let tree', to_branch =
    if bval then Execution_tree.move_true !tree
    else Execution_tree.move_false !tree
  in
  tree := tree';
  if to_branch then Some (insert_pc ~neg:bval c pc) else None

let rec step (c : config) : config =
  let { frame; glob; code = vs, es; mem; store; heap; pc; bp; tree; _ } = c in
  let e = List.hd es in
  let vs', es', pc', bp' =
    match (e.it, vs) with
    | Plain e', vs -> (
        match (e', vs) with
        | Unreachable, vs ->
            (vs, [ Trapping "unreachable executed" @@ e.at ], pc, bp)
        | Nop, vs -> (vs, [], pc, bp)
        | Block (ts, es'), vs ->
            let es' =
              [ Label (List.length ts, [], ([], List.map plain es')) @@ e.at ]
            in
            (vs, es', pc, bp)
        | Loop (ts, es'), vs ->
            ( vs,
              [ Label (0, [ e' @@ e.at ], ([], List.map plain es')) @@ e.at ],
              pc,
              bp )
        | If (ts, es1, es2), (I32 i, ex) :: vs' when is_concrete (simplify ex)
          ->
            if i = 0l then (vs', [ Plain (Block (ts, es2)) @@ e.at ], pc, bp)
            else (vs', [ Plain (Block (ts, es1)) @@ e.at ], pc, bp)
        | If (ts, es1, es2), (I32 i, ex) :: vs' ->
            if i = 0l then
              let bp' =
                Batteries.Option.map_default
                  (fun br -> br :: bp)
                  bp
                  (branch_on_cond false ex pc tree)
              in
              let pc' = insert_pc ~neg:true ex pc in
              (vs', [ Plain (Block (ts, es2)) @@ e.at ], pc', bp')
            else
              let bp' =
                Batteries.Option.map_default
                  (fun br -> br :: bp)
                  bp
                  (branch_on_cond true ex pc tree)
              in
              let pc' = insert_pc ex pc in
              (vs', [ Plain (Block (ts, es1)) @@ e.at ], pc', bp')
        | Br x, vs -> ([], [ Breaking (x.it, vs) @@ e.at ], pc, bp)
        | BrIf x, (I32 i, ex) :: vs' when is_concrete (simplify ex) ->
            if i = 0l then (vs', [], pc, bp)
            else (vs', [ Plain (Br x) @@ e.at ], pc, bp)
        | BrIf x, (I32 i, ex) :: vs' ->
            if i = 0l then
              let bp' =
                Batteries.Option.map_default
                  (fun br -> br :: bp)
                  bp
                  (branch_on_cond false ex pc tree)
              in
              let pc' = insert_pc ~neg:true ex pc in
              (vs', [], pc', bp')
            else
              let bp' =
                Batteries.Option.map_default
                  (fun br -> br :: bp)
                  bp
                  (branch_on_cond true ex pc tree)
              in
              let pc' = insert_pc ex pc in
              (vs', [ Plain (Br x) @@ e.at ], pc', bp')
        | BrTable (xs, x), (I32 i, _) :: vs'
          when Interpreter.I32.ge_u i (Interpreter.Lib.List32.length xs) ->
            (vs', [ Plain (Br x) @@ e.at ], pc, bp)
        | BrTable (xs, x), (I32 i, _) :: vs' ->
            ( vs',
              [ Plain (Br (Interpreter.Lib.List32.nth xs i)) @@ e.at ],
              pc,
              bp )
        | Return, vs -> ([], [ Returning vs @@ e.at ], pc, bp)
        | Call x, vs -> (vs, [ Invoke (func frame.inst x) @@ e.at ], pc, bp)
        | CallIndirect x, (I32 i, _) :: vs ->
            let func = func_elem frame.inst (0l @@ e.at) i e.at in
            if type_ frame.inst x <> Interpreter.Func.type_of func then
              (vs, [ Trapping "indirect call type mismatch" @@ e.at ], pc, bp)
            else (vs, [ Invoke func @@ e.at ], pc, bp)
        | Drop, v :: vs' -> (vs', [], pc, bp)
        | Select, (I32 i, ve) :: v2 :: v1 :: vs' when is_concrete (simplify ve)
          ->
            if i = 0l then (v2 :: vs', [], pc, bp) else (v1 :: vs', [], pc, bp)
        | Select, (I32 i, ve) :: v2 :: v1 :: vs' ->
            if i = 0l then
              let bp' =
                Batteries.Option.map_default
                  (fun br -> br :: bp)
                  bp
                  (branch_on_cond false ve pc tree)
              in
              (v2 :: vs', [], insert_pc ~neg:true ve pc, bp')
            else
              let bp' =
                Batteries.Option.map_default
                  (fun br -> br :: bp)
                  bp
                  (branch_on_cond true ve pc tree)
              in
              (v1 :: vs', [], insert_pc ve pc, bp')
        | LocalGet x, vs -> (!(local frame x) :: vs, [], pc, bp)
        | LocalSet x, (v, ex) :: vs' ->
            local frame x := (v, simplify ex);
            (vs', [], pc, bp)
        | LocalTee x, (v, ex) :: vs' ->
            local frame x := (v, simplify ex);
            (!(local frame x) :: vs', [], pc, bp)
        | GlobalGet x, vs -> (Globals.find glob x.it :: vs, [], pc, bp)
        | GlobalSet x, v :: vs' ->
            Globals.add glob x.it v;
            (vs', [], pc, bp)
        | Load { offset; ty; sz; _ }, (I32 i, sym_ptr) :: vs' -> (
            let base = Interpreter.I64_convert.extend_i32_u i in
            (* overflow check *)
            let ptr = get_ptr (simplify sym_ptr) in
            try
              (if Option.is_some ptr then
               let low =
                 Interpreter.Values.I32Value.of_value
                   (Evaluations.to_value (Option.get ptr))
               in
               let chunk_size =
                 try Hashtbl.find heap low
                 with Not_found -> raise (BugException (c, e.at, UAF))
               in
               let high = Int64.(add (of_int32 low) (of_int32 chunk_size))
               and ptr_val = Int64.(add base (of_int32 offset)) in
               (* ptr_val \notin [low, high[ => overflow *)
               if ptr_val < Int64.of_int32 low || ptr_val >= high then
                 raise (BugException (c, e.at, Overflow)));
              let v, e =
                match sz with
                | None ->
                    Heap.load_value mem base offset (Evaluations.to_num_type ty)
                | Some (sz, ext) ->
                    Heap.load_packed sz ext mem base offset
                      (Evaluations.to_num_type ty)
              in
              ((v, e) :: vs', [], pc, bp)
            with
            | BugException (_, at, b) ->
                (vs', [ Interrupt (Bug b) @@ e.at ], pc, bp)
            | exn -> (vs', [ Trapping (memory_error e.at exn) @@ e.at ], pc, bp)
            )
        | Store { offset; sz; _ }, (v, ex) :: (I32 i, sym_ptr) :: vs' -> (
            let base = Interpreter.I64_convert.extend_i32_u i in
            let ptr = get_ptr (simplify sym_ptr) in
            try
              (if Option.is_some ptr then
               let low =
                 Interpreter.Values.I32Value.of_value
                   (Evaluations.to_value (Option.get ptr))
               in
               let chunk_size =
                 try Hashtbl.find heap low
                 with Not_found -> raise (BugException (c, e.at, UAF))
               in
               let high = Int64.(add (of_int32 low) (of_int32 chunk_size))
               and ptr_val = Int64.(add base (of_int32 offset)) in
               if Int64.of_int32 low > ptr_val || ptr_val >= high then
                 raise (BugException (c, e.at, Overflow)));
              (match sz with
              | None -> Heap.store_value mem base offset (v, simplify ex)
              | Some sz -> Heap.store_packed sz mem base offset (v, simplify ex));
              (vs', [], pc, bp)
            with
            | BugException (_, at, b) ->
                (vs', [ Interrupt (Bug b) @@ e.at ], pc, bp)
            | exn -> (vs', [ Trapping (memory_error e.at exn) @@ e.at ], pc, bp)
            )
        | MemorySize, vs ->
            let mem' = memory frame.inst (0l @@ e.at) in
            let v : Num.t = I32 (Interpreter.Memory.size mem') in
            ((v, Num v) :: vs, [], pc, bp)
        | MemoryGrow, (I32 delta, _) :: vs' ->
            let mem' = memory frame.inst (0l @@ e.at) in
            let old_size = Interpreter.Memory.size mem' in
            let result =
              let open Interpreter in
              try
                Memory.grow mem' delta;
                old_size
              with
              | Memory.SizeOverflow | Memory.SizeLimit | Memory.OutOfMemory ->
                -1l
            in
            ((I32 result, Num (I32 result)) :: vs', [], pc, bp)
        | Const v, vs ->
            let v' = Evaluations.of_value v.it in
            ((v', Num v') :: vs, [], pc, bp)
        | Test testop, v :: vs' -> (
            try (eval_testop v testop :: vs', [], pc, bp)
            with exn ->
              (vs', [ Trapping (numeric_error e.at exn) @@ e.at ], pc, bp))
        | Compare relop, v2 :: v1 :: vs' -> (
            try (eval_relop v1 v2 relop :: vs', [], pc, bp)
            with exn ->
              (vs', [ Trapping (numeric_error e.at exn) @@ e.at ], pc, bp))
        | Unary unop, v :: vs' -> (
            try (eval_unop v unop :: vs', [], pc, bp)
            with exn ->
              (vs', [ Trapping (numeric_error e.at exn) @@ e.at ], pc, bp))
        | Binary binop, v2 :: v1 :: vs' -> (
            try (eval_binop v1 v2 binop :: vs', [], pc, bp)
            with exn ->
              (vs', [ Trapping (numeric_error e.at exn) @@ e.at ], pc, bp))
        | Convert cvtop, v :: vs' -> (
            try (eval_cvtop cvtop v :: vs', [], pc, bp)
            with exn ->
              (vs', [ Trapping (numeric_error e.at exn) @@ e.at ], pc, bp))
        | Dup, v :: vs' -> (v :: v :: vs', [], pc, bp)
        | SymAssert, (I32 0l, ex) :: vs' ->
            debug ">>> Assert FAILED! Stopping...";
            (vs', [ Interrupt (Failure pc) @@ e.at ], pc, bp)
        | SymAssert, (I32 i, ex) :: vs' when is_concrete (simplify ex) ->
            (vs', [], pc, bp)
        | SymAssert, (I32 i, ex) :: vs' ->
            let formulas = insert_pc ~neg:true ex pc in
            if not (Encoding.Batch.check solver formulas) then (vs', [], pc, bp)
            else
              let binds =
                Encoding.Batch.(
                  model_binds (get_model solver) (Store.get_key_types store))
              in
              Store.update store binds;
              (vs', [ Interrupt (Failure pc) @@ e.at ], pc, bp)
        | SymAssume, (I32 i, ex) :: vs' when is_concrete (simplify ex) ->
            let unsat = Relop (I32 I32.Eq, Num (I32 0l), Num (I32 1l)) in
            if i = 0l then (vs', [ Restart [ unsat ] @@ e.at ], pc, bp)
            else (vs', [], pc, bp)
        | SymAssume, (I32 i, ex) :: vs' ->
            if i = 0l then (vs', [ Restart (insert_pc ex pc) @@ e.at ], pc, bp)
            else (
              debug ">>> Assume passed. Continuing execution...";
              let tree', _ = Execution_tree.move_true !tree in
              tree := tree';
              (vs', [], insert_pc ex pc, bp))
        | Symbolic (ty, b), (I32 i, _) :: vs' ->
            let base = Interpreter.I64_convert.extend_i32_u i in
            let symbol = if i = 0l then "x" else Heap.load_string mem base in
            let x = Store.next store symbol in
            let ty' = Evaluations.to_num_type ty in
            let v = Store.get store x ty' b in
            ((v, symbolic ty' x) :: vs', [], pc, bp)
        | Boolop boolop, (v2, sv2) :: (v1, sv1) :: vs' -> (
            let sv2' = mk_relop sv2 (Types.type_of_num v2) in
            let v2' =
              Num.(num_of_bool (not (v2 = default_value (type_of_num v2))))
            in
            let sv1' = mk_relop sv1 (Types.type_of_num v1) in
            let v1' =
              Num.(num_of_bool (not (v1 = default_value (type_of_num v1))))
            in
            try
              let v3, sv3 = eval_binop (v1', sv1') (v2', sv2') boolop in
              ((v3, simplify sv3) :: vs', [], pc, bp)
            with exn ->
              (vs', [ Trapping (numeric_error e.at exn) @@ e.at ], pc, bp))
        | Alloc, (I32 a, sa) :: (I32 b, sb) :: vs' ->
            Hashtbl.add heap b a;
            ((I32 b, SymPtr (b, Num (I32 0l))) :: vs', [], pc, bp)
        | Free, (I32 i, _) :: vs' ->
            let es' =
              if not (Hashtbl.mem heap i) then
                [ Interrupt (Bug InvalidFree) @@ e.at ]
              else (
                Hashtbl.remove heap i;
                [])
            in
            (vs', es', pc, bp)
        | GetSymInt32 x, vs' ->
            let v =
              try Store.find store x
              with Not_found ->
                Crash.error e.at "Symbolic variable was not in store."
            in
            ((v, symbolic `I32Type x) :: vs', [], pc, bp)
        | GetSymInt64 x, vs' ->
            let v =
              try Store.find store x
              with Not_found ->
                Crash.error e.at "Symbolic variable was not in store."
            in
            ((v, symbolic `I64Type x) :: vs', [], pc, bp)
        | GetSymFloat32 x, vs' ->
            let v =
              try Store.find store x
              with Not_found ->
                Crash.error e.at "Symbolic variable was not in store."
            in
            ((v, symbolic `F32Type x) :: vs', [], pc, bp)
        | GetSymFloat64 x, vs' ->
            let v =
              try Store.find store x
              with Not_found ->
                Crash.error e.at "Symbolic variable was not in store."
            in
            ((v, symbolic `F64Type x) :: vs', [], pc, bp)
        | TernaryOp, (I32 r2, s_r2) :: (I32 r1, s_r1) :: (I32 c, s_c) :: vs' ->
            let r : Num.t = I32 (if c = 0l then r2 else r1) in
            let s_c' = to_relop (simplify s_c) in
            let v, pc' =
              match s_c' with
              | None -> ((r, if c = 0l then s_r2 else s_r1), pc)
              | Some s ->
                  let x = Store.next store "__ternary" in
                  Store.add store x r;
                  let s_x = symbolic `I32Type x in
                  let t_eq = Relop (I32 I32.Eq, s_x, s_r1) in
                  let t_imp = Binop (I32 I32.Or, negate_relop s, t_eq) in
                  let f_eq = Relop (I32 I32.Eq, s_x, s_r2) in
                  let f_imp = Binop (I32 I32.Or, s, f_eq) in
                  let cond = Binop (I32 I32.And, t_imp, f_imp) in
                  ((r, s_x), Relop (I32 I32.Ne, cond, Num (I32 0l)) :: pc)
            in
            (v :: vs', [], pc', bp)
        | PrintStack, vs' ->
            debug
              (Interpreter.Source.string_of_pos e.at.left
              ^ ":VS:\n"
              ^ Expression.string_of_values vs');
            (vs', [], pc, bp)
        | PrintPC, vs' ->
            debug
              (Interpreter.Source.string_of_pos e.at.left
              ^ ":PC: "
              ^ Encoding.Formula.(pp_to_string (to_formula pc)));
            (vs', [], pc, bp)
        | PrintMemory, vs' ->
            debug ("Mem:\n" ^ Heap.to_string mem);
            (vs', [], pc, bp)
        | PrintBtree, vs' ->
            Printf.printf "B TREE STATE: \n\n";
            (* Btree.print_b_tree mem; *)
            (vs', [], pc, bp)
        | CompareExpr, (v1, ex1) :: (v2, ex2) :: vs' ->
            let res : Num.t * Expression.t =
              match (ex1, ex2) with
              | Symbolic (`I32Type, x), Symbolic (`I32Type, y) ->
                  if x = y then (I32 1l, Relop (I32 I32.Eq, ex1, ex2))
                  else (I32 0l, Relop (I32 I32.Ne, ex1, ex2))
              | _, _ ->
                  eval_relop (v1, ex1) (v2, ex2)
                    (Interpreter.Values.I32 Interpreter.Ast.I32Op.Eq)
            in
            (res :: vs', [], pc, bp)
        | IsSymbolic, (I32 n, _) :: (I32 i, _) :: vs' ->
            let base = Interpreter.I64_convert.extend_i32_u i in
            let _, v = Heap.load_bytes mem base (Int32.to_int n) in
            let result : Num.t = I32 (match v with Num _ -> 0l | _ -> 1l) in
            ((result, Num result) :: vs', [], pc, bp)
        | SetPriority, _ :: _ :: _ :: vs' -> (vs', [], pc, bp)
        | PopPriority, _ :: vs' -> (vs', [], pc, bp)
        | _ -> Crash.error e.at "missing or ill-typed operand on stack")
    | Trapping msg, vs -> assert false
    | Interrupt i, vs -> assert false
    | Restart pc, vs -> assert false
    | Returning vs', vs -> Crash.error e.at "undefined frame"
    | Breaking (k, vs'), vs -> Crash.error e.at "undefined label"
    | Label (n, es0, (vs', [])), vs -> (vs' @ vs, [], pc, bp)
    | Label (n, es0, (vs', { it = Restart pc; at } :: es')), vs ->
        (vs, [ Restart pc @@ at; Label (n, es0, (vs', es')) @@ e.at ], pc, bp)
    | Label (n, es0, (vs', { it = Interrupt i; at } :: es')), vs ->
        (vs, [ Interrupt i @@ at; Label (n, es0, (vs', es')) @@ e.at ], pc, bp)
    | Label (n, es0, (vs', { it = Trapping msg; at } :: es')), vs ->
        (vs, [ Trapping msg @@ at ], pc, bp)
    | Label (n, es0, (vs', { it = Returning vs0; at } :: es')), vs ->
        (vs, [ Returning vs0 @@ at ], pc, bp)
    | Label (n, es0, (vs', { it = Breaking (0l, vs0); at } :: es')), vs ->
        (take n vs0 e.at @ vs, List.map plain es0, pc, bp)
    | Label (n, es0, (vs', { it = Breaking (k, vs0); at } :: es')), vs ->
        (vs, [ Breaking (Int32.sub k 1l, vs0) @@ at ], pc, bp)
    | Label (n, es0, code'), vs ->
        let c' = step { c with code = code' } in
        (vs, [ Label (n, es0, c'.code) @@ e.at ], c'.pc, c'.bp)
    | Frame (n, frame', (vs', [])), vs -> (vs' @ vs, [], pc, bp)
    | Frame (n, frame', (vs', { it = Restart pc; at } :: es')), vs ->
        (vs, [ Restart pc @@ at; Frame (n, frame', (vs', es')) @@ e.at ], pc, bp)
    | Frame (n, frame', (vs', { it = Interrupt i; at } :: es')), vs ->
        ( vs,
          [ Interrupt i @@ at; Frame (n, frame', (vs', es')) @@ e.at ],
          pc,
          bp )
    | Frame (n, frame', (vs', { it = Trapping msg; at } :: es')), vs ->
        (vs, [ Trapping msg @@ at ], pc, bp)
    | Frame (n, frame', (vs', { it = Returning vs0; at } :: es')), vs ->
        (take n vs0 e.at @ vs, [], pc, bp)
    | Frame (n, frame', code'), vs ->
        let c' =
          step
            {
              frame = frame';
              glob = c.glob;
              code = code';
              mem = c.mem;
              heap = c.heap;
              store = c.store;
              pc = c.pc;
              bp = c.bp;
              tree = c.tree;
              budget = c.budget - 1;
            }
        in
        (vs, [ Frame (n, c'.frame, c'.code) @@ e.at ], c'.pc, c'.bp)
    | Invoke func, vs when c.budget = 0 ->
        Exhaustion.error e.at "call stack exhausted"
    | Invoke func, vs -> (
        let symbolic_arg t =
          let x = Store.next store "arg" in
          let v = Store.get store x t false in
          (v, symbolic t x)
        in
        let (Interpreter.Types.FuncType (ins, out)) =
          Interpreter.Func.type_of func
        in
        let n = List.length ins in
        let vs =
          if n > 0 && List.length vs = 0 then
            List.map (fun t -> symbolic_arg (Evaluations.to_num_type t)) ins
          else vs
        in
        let args, vs' = (take n vs e.at, drop n vs e.at) in
        match func with
        | Interpreter.Func.AstFunc (t, inst', f) ->
            let locals' =
              List.map
                (fun v -> (v, Num v))
                (List.map
                   (fun t -> Num.default_value (Evaluations.to_num_type t))
                   f.it.locals)
            in
            let locals'' = List.rev args @ locals' in
            let code' = ([], [ Plain (Block (out, f.it.body)) @@ f.at ]) in
            let frame' = { inst = !inst'; locals = List.map ref locals'' } in
            (vs', [ Frame (List.length out, frame', code') @@ e.at ], pc, bp)
        | Interpreter.Func.HostFunc (t, f) -> failwith "HostFunc error")
  in
  let e' =
    step_cnt := !step_cnt + 1;
    if
      (not (!Interpreter.Flags.inst_limit = -1))
      && !step_cnt >= !Interpreter.Flags.inst_limit
    then [ Interrupt Limit @@ e.at ]
    else []
  in
  { c with code = (vs', e' @ es' @ List.tl es); pc = pc'; bp = bp' }

let get_reason (err_t, at) : string =
  let loc =
    Interpreter.Source.string_of_pos at.left
    ^ if at.right = at.left then "" else "-" ^ string_of_pos at.right
  in
  "{" ^ "\"type\" : \"" ^ err_t ^ "\", " ^ "\"line\" : \"" ^ loc ^ "\"" ^ "}"

let write_test_case ?(witness = false) out_dir test_data cnt : unit =
  if not (test_data = "[]") then
    let i = cnt () in
    let filename =
      if witness then Printf.sprintf "%s/witness_%05d.json" out_dir i
      else Printf.sprintf "%s/test_%05d.json" out_dir i
    in
    Interpreter.Io.save_file filename test_data

let write_report error loop_time : unit =
  let spec, reason =
    match error with None -> (true, "{}") | Some e -> (false, get_reason e)
  in
  let report_str =
    "{" ^ "\"specification\": " ^ string_of_bool spec ^ ", " ^ "\"reason\" : "
    ^ reason ^ ", " ^ "\"loop_time\" : \"" ^ string_of_float loop_time ^ "\", "
    ^ "\"solver_time\" : \""
    ^ string_of_float !Encoding.Batch.time_solver
    ^ "\", " ^ "\"paths_explored\" : " ^ string_of_int !iterations ^ ", "
    ^ "\"solver_counter\" : " ^ string_of_int !solver_cnt ^ ", "
    ^ "\"instruction_counter\" : " ^ string_of_int !step_cnt ^ "}"
  in
  Interpreter.Io.save_file
    (Filename.concat !Interpreter.Flags.output "report.json")
    report_str

let rec update_admin_instr f e =
  let it =
    match e.it with
    | Plain e -> Plain e
    | Invoke f -> Invoke f
    | Trapping exn -> Trapping exn
    | Returning vs -> Returning (List.map f vs)
    | Breaking (n, vs) -> Breaking (n, List.map f vs)
    | Label (n, es0, (vs, es)) ->
        Label (n, es0, (List.map f vs, List.map (update_admin_instr f) es))
    | Frame (n, frame, (vs, es)) ->
        List.iter (fun l -> l := f !l) frame.locals;
        Frame (n, frame, (List.map f vs, List.map (update_admin_instr f) es))
    | Interrupt i -> Interrupt i
    | Restart pc -> Restart pc
  in
  { it; at = e.at }

let update c (vs, es) pc =
  let binds =
    Encoding.Batch.(
      model_binds (get_model solver) (Store.get_key_types c.store))
  in
  let tree', _ = Execution_tree.move_true !(c.tree) in
  c.tree := tree';
  Store.update c.store binds;
  Heap.update c.mem c.store;
  let f store (_, expr) = (Store.eval store expr, expr) in
  List.iter (fun l -> l := f c.store !l) c.frame.locals;
  let code =
    (List.map (f c.store) vs, List.map (update_admin_instr (f c.store)) es)
  in
  { c with code; pc }

let reset c glob code mem =
  let binds =
    Encoding.Batch.(
      model_binds (get_model solver) (Store.get_key_types c.store))
  in
  Store.reset c.store;
  Store.init c.store binds;
  Globals.clear c.glob;
  Globals.add_seq c.glob (Globals.to_seq glob);
  Heap.clear c.mem;
  Heap.add_seq c.mem (Heap.to_seq mem);
  Hashtbl.reset c.heap;
  c.tree := head;
  {
    c with
    frame = frame empty_module_inst [];
    code;
    pc = [];
    bp = [];
    budget = 100000;
  }

module type Work_list = sig
  type 'a t

  exception Empty

  val create : unit -> 'a t
  val pop : 'a t -> 'a
  val push : 'a -> 'a t -> unit
  val is_empty : 'a t -> bool
end

module Guided_search (L : Work_list) = struct
  let invoke (c : config) (test_suite : string) =
    let cntr = count 0 in
    let glob0 = Globals.copy c.glob
    and code0 = c.code
    and mem0 = Heap.memcpy c.mem in
    let wl = L.create () in
    let rec eval (c : config) : config =
      match c.code with
      | vs, [] -> c
      | vs, { it = Trapping msg; at } :: _ -> Trap.error at msg
      | vs, { it = Restart pc; at } :: es -> c
      | vs, { it = Interrupt i; at } :: es -> c
      | vs, es ->
          let c' = step c in
          List.iter (fun pc -> L.push pc wl) c'.bp;
          eval { c' with bp = [] }
    in
    let rec find_sat_pc pcs =
      if L.is_empty pcs then false
      else if not (Encoding.Batch.check solver (L.pop pcs)) then find_sat_pc pcs
      else true
    in
    (* Main concolic loop *)
    let rec loop c =
      iterations := !iterations + 1;
      let { code; store; bp; _ } = eval c in
      List.iter (fun pc -> L.push pc wl) bp;
      match code with
      | vs, { it = Interrupt Limit; at } :: _ -> None
      | vs, { it = Interrupt i; at } :: _ ->
          write_test_case test_suite ~witness:true (Store.to_json store) cntr;
          Some (string_of_interruption i, at)
      | vs, { it = Restart pc; _ } :: es ->
          iterations := !iterations - 1;
          if Encoding.Batch.check solver pc then loop (update c (vs, es) pc)
          else if L.is_empty wl || not (find_sat_pc wl) then None
          else loop (reset c glob0 code0 mem0)
      | _ ->
          write_test_case test_suite (Store.to_json store) cntr;
          if L.is_empty wl || not (find_sat_pc wl) then None
          else loop (reset c glob0 code0 mem0)
    in
    loop_start := Sys.time ();
    let error = loop c in
    write_report error (Sys.time () -. !loop_start)
end

module DFS = Guided_search (Stack)
module BFS = Guided_search (Queue)
module RND = Guided_search (RandArray)

let set_timeout (time_limit : int) : unit =
  let alarm_handler i : unit =
    Encoding.Batch.interrupt ();
    let loop_time = Sys.time () -. !loop_start in
    write_report None loop_time;
    exit 0
  in
  if time_limit > 0 then (
    Sys.(set_signal sigalrm (Signal_handle alarm_handler));
    ignore (Unix.alarm time_limit))

let main (func : func_inst) (vs : value list) (inst : module_inst)
    (mem0 : Heap.t) =
  let open Interpreter in
  set_timeout !Flags.timeout;
  let test_suite = Filename.concat !Flags.output "test_suite" in
  Io.safe_mkdir test_suite;
  let at = match func with Func.AstFunc (_, _, f) -> f.at | _ -> no_region in
  let glob = Globals.create () in
  Globals.add_seq glob
    (List.to_seq
       (List.mapi
          (fun i a ->
            let v = Global.load a in
            (Int32.of_int i, (of_value v, Num (of_value v))))
          inst.globals));
  let c =
    config empty_module_inst (List.rev vs)
      [ Invoke func @@ at ]
      mem0 glob (ref head)
  in
  let f =
    match parse_policy !Flags.policy with
    | None -> Crash.error at ("invalid search policy '" ^ !Flags.policy ^ "'")
    | Some Depth -> DFS.invoke
    | Some Breadth -> BFS.invoke
    | Some Random -> RND.invoke
  in
  f c test_suite

let i32 (v : Interpreter.Values.value) at =
  match v with
  | Interpreter.Values.I32 i -> i
  | _ -> Crash.error at "type error: i32 value expected"

let create_func (inst : module_inst) (f : func) : func_inst =
  Interpreter.Func.alloc (type_ inst f.it.ftype) (ref inst) f

let create_table (inst : module_inst) (tab : table) : table_inst =
  let { ttype } = tab.it in
  Interpreter.Table.alloc ttype

let create_memory (inst : module_inst) (mem : memory) : memory_inst =
  let { mtype } = mem.it in
  Interpreter.Memory.alloc mtype

let create_global (inst : module_inst) (glob : global) : global_inst =
  let { gtype; value } = glob.it in
  let v = Interpreter.Eval.eval_const inst value in
  Interpreter.Global.alloc gtype v

let create_export (inst : module_inst) (ex : export) : export_inst =
  let { name; edesc } = ex.it in
  let ext =
    match edesc.it with
    | FuncExport x -> ExternFunc (func inst x)
    | TableExport x -> ExternTable (table inst x)
    | MemoryExport x -> ExternMemory (memory inst x)
    | GlobalExport x -> ExternGlobal (global inst x)
  in
  (name, ext)

let init_func (inst : module_inst) (func : func_inst) =
  match func with
  | Interpreter.Func.AstFunc (_, inst_ref, _) -> inst_ref := inst
  | _ -> assert false

let init_table (inst : module_inst) (seg : table_segment) =
  let open Interpreter in
  let { index; offset = const; init } = seg.it in
  let tab = table inst index in
  let offset = i32 (Eval.eval_const inst const) const.at in
  let end_ = Int32.(add offset (of_int (List.length init))) in
  let bound = Table.size tab in
  if I32.lt_u bound end_ || I32.lt_u end_ offset then
    Link.error seg.at "elements segment does not fit table";
  fun () ->
    Table.blit tab offset (List.map (fun x -> FuncElem (func inst x)) init)

let init_memory (inst : module_inst) (sym_mem : Heap.t) (seg : memory_segment) =
  let open Interpreter in
  let { index; offset = const; init } = seg.it in
  let mem = memory inst index in
  let offset' = i32 (Eval.eval_const inst const) const.at in
  let offset = I64_convert.extend_i32_u offset' in
  let end_ = Int64.(add offset (of_int (String.length init))) in
  let bound = Memory.bound mem in
  if I64.lt_u bound end_ || I64.lt_u end_ offset then
    Link.error seg.at "data segment does not fit memory";
  fun () -> Heap.store_bytes sym_mem offset init

let add_import (m : module_) (ext : extern) (im : import) (inst : module_inst) :
    module_inst =
  let open Interpreter in
  if not (Types.match_extern_type (extern_type_of ext) (import_type m im)) then
    Link.error im.at "incompatible import type";
  match ext with
  | ExternFunc func -> { inst with funcs = func :: inst.funcs }
  | ExternTable tab -> { inst with tables = tab :: inst.tables }
  | ExternMemory mem -> { inst with memories = mem :: inst.memories }
  | ExternGlobal glob -> { inst with globals = glob :: inst.globals }

let init (m : module_) (exts : extern list) =
  let open Interpreter in
  let {
    imports;
    tables;
    memories;
    globals;
    funcs;
    types;
    exports;
    elems;
    data;
    start;
  } =
    m.it
  in
  if List.length exts <> List.length imports then
    Link.error m.at "wrong number of imports provided for initialisation";
  let inst0 =
    {
      (List.fold_right2 (add_import m) exts imports empty_module_inst) with
      types = List.map (fun type_ -> type_.it) types;
    }
  in
  let fs = List.map (create_func inst0) funcs in
  let inst1 =
    {
      inst0 with
      funcs = inst0.funcs @ fs;
      tables = inst0.tables @ List.map (create_table inst0) tables;
      memories = inst0.memories @ List.map (create_memory inst0) memories;
      globals = inst0.globals @ List.map (create_global inst0) globals;
    }
  in
  let inst = { inst1 with exports = List.map (create_export inst1) exports } in
  List.iter (init_func inst) fs;
  let init_elems = List.map (init_table inst) elems in
  let memory = Heap.alloc Flags.hashtbl_default_size in
  let init_datas = List.map (init_memory inst memory) data in
  List.iter (fun f -> f ()) init_elems;
  List.iter (fun f -> f ()) init_datas;
  Lib.Option.app (fun x -> ignore (main (func inst x) [] inst memory)) start;
  (memory, inst)
