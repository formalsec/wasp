open Values
open Symvalue
open Types
open Instance
open Ast
open Source
open Evaluations
open Si32
module Link = Error.Make ()
module Trap = Error.Make ()
module Crash = Error.Make ()
module Exhaustion = Error.Make ()

exception Link = Link.Error
exception Trap = Trap.Error
exception Crash = Crash.Error
exception Exhaustion = Exhaustion.Error

let memory_error at = function
  | Heap.InvalidAddress a ->
      Int64.to_string a ^ ":address not found in hashtable"
  | Heap.Bounds -> "out of bounds memory access"
  | Memory.SizeOverflow -> "memory size overflow"
  | Memory.SizeLimit -> "memory size limit reached"
  | Memory.Type -> Crash.error at "type mismatch at memory access"
  | exn -> raise exn

let numeric_error at = function
  | Evaluations.UnsupportedOp m -> m ^ ": unsupported operation"
  | Numeric_error.IntegerOverflow -> "integer overflow"
  | Numeric_error.IntegerDivideByZero -> "integer divide by zero"
  | Numeric_error.InvalidConversionToInteger -> "invalid conversion to integer"
  | Eval_numeric.TypeError (i, v, t) ->
      Crash.error at
        ("type error, expected "
        ^ Types.string_of_value_type t
        ^ " as operand " ^ string_of_int i ^ ", got "
        ^ Types.string_of_value_type (Values.type_of v))
  | exn -> raise exn

type policy = Random | Depth | Breadth
type bug = Overflow | UAF | InvalidFree

type interruption =
  | IntLimit
  | AssFail of path_conditions
  | AsmFail of path_conditions
  | Bug of bug

type 'a stack = 'a list
type frame = { inst : module_inst; locals : sym_value ref list }
type pc = sym_expr list

type code = sym_value stack * sym_admin_instr list
and sym_admin_instr = sym_admin_instr' phrase

and sym_admin_instr' =
  | SPlain of instr'
  | SInvoke of func_inst
  | STrapping of string
  | SReturning of sym_value stack
  | SBreaking of int32 * sym_value stack
  | SLabel of int * instr list * code
  | SFrame of int * frame * code
  | Interrupt of interruption

type config = {
  frame : frame;
  glob : Globals.t;
  code : code;
  mem : Heap.t;
  store : Store.t;
  heap : (int32, int32) Hashtbl.t;
  pc : pc;
  bp : sym_expr list list;
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
    heap = Hashtbl.create 128;
    pc = [];
    bp = [];
    tree;
    budget = 100000;
  }

exception InstrLimit of config
exception AssumeFail of config * path_conditions
exception AssertFail of config * region
exception BugException of config * region * bug
exception Unsatisfiable

let head = ref Execution_tree.Leaf
let step_cnt = ref 0
let solver_cnt = ref 0
let iterations = ref 0
let solver_time = ref 0.
let loop_start = ref 0.
let debug str = if !Flags.trace then print_endline str

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

let plain e = SPlain e.it @@ e.at

let lookup category list x =
  try Lib.List32.nth list x.it
  with Failure _ ->
    Crash.error x.at ("undefined " ^ category ^ " " ^ Int32.to_string x.it)

let type_ (inst : module_inst) x = lookup "type" inst.types x
let func (inst : module_inst) x = lookup "function" inst.funcs x
let table (inst : module_inst) x = lookup "table" inst.tables x
let memory (inst : module_inst) x = lookup "memory" inst.memories x
let global (inst : module_inst) x = lookup "global" inst.globals x
let local (frame : frame) x = lookup "local" frame.locals x

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
  | _ -> "not support"

let timed_check_sat formulas =
  let start = Sys.time () in
  let opt_model = Encoding.check formulas in
  let delta = Sys.time () -. start in
  solver_time := !solver_time +. delta;
  solver_cnt := !solver_cnt + 1;
  opt_model

let branch_on_cond bval c pc tree =
  let tree', to_branch =
    if bval then Execution_tree.move_true !tree
    else Execution_tree.move_false !tree
  in
  tree := tree';
  if to_branch then add_constraint ~neg:bval c pc else []

let rec step (c : config) : config =
  let { frame; glob; code = vs, es; mem; store; heap; pc; bp; tree; _ } = c in
  let e = List.hd es in
  let vs', es', pc', bp' =
    match (e.it, vs) with
    | SPlain e', vs -> (
        match (e', vs) with
        | Unreachable, vs ->
            (vs, [ STrapping "unreachable executed" @@ e.at ], pc, bp)
        | Nop, vs -> (vs, [], pc, bp)
        | Block (ts, es'), vs ->
            let es' =
              [ SLabel (List.length ts, [], ([], List.map plain es')) @@ e.at ]
            in
            (vs, es', pc, bp)
        | Loop (ts, es'), vs ->
            ( vs,
              [ SLabel (0, [ e' @@ e.at ], ([], List.map plain es')) @@ e.at ],
              pc,
              bp )
        | If (ts, es1, es2), (I32 0l, ex) :: vs' when is_concrete (simplify ex)
          ->
            (vs', [ SPlain (Block (ts, es2)) @@ e.at ], pc, bp)
        | If (ts, es1, es2), (I32 0l, ex) :: vs' ->
            let br = branch_on_cond false ex pc tree in
            let pc' = add_constraint ~neg:true ex pc in
            (vs', [ SPlain (Block (ts, es2)) @@ e.at ], pc', br :: bp)
        | If (ts, es1, es2), (I32 i, ex) :: vs' when is_concrete (simplify ex)
          ->
            (vs', [ SPlain (Block (ts, es1)) @@ e.at ], pc, bp)
        | If (ts, es1, es2), (I32 i, ex) :: vs' ->
            let br = branch_on_cond true ex pc tree in
            let pc' = add_constraint ex pc in
            (vs', [ SPlain (Block (ts, es1)) @@ e.at ], pc', br :: bp)
        | Br x, vs -> ([], [ SBreaking (x.it, vs) @@ e.at ], pc, bp)
        | BrIf x, (I32 0l, ex) :: vs' when is_concrete (simplify ex) ->
            (vs', [], pc, bp)
        | BrIf x, (I32 0l, ex) :: vs' ->
            let br = branch_on_cond false ex pc tree in
            let pc' = add_constraint ~neg:true ex pc in
            (vs', [], pc', br :: bp)
        | BrIf x, (I32 i, ex) :: vs' when is_concrete (simplify ex) ->
            (vs', [ SPlain (Br x) @@ e.at ], pc, bp)
        | BrIf x, (I32 i, ex) :: vs' ->
            let br = branch_on_cond true ex pc tree in
            let pc' = add_constraint ex pc in
            (vs', [ SPlain (Br x) @@ e.at ], pc', br :: bp)
        | BrTable (xs, x), (I32 i, _) :: vs'
          when I32.ge_u i (Lib.List32.length xs) ->
            (vs', [ SPlain (Br x) @@ e.at ], pc, bp)
        | BrTable (xs, x), (I32 i, _) :: vs' ->
            (vs', [ SPlain (Br (Lib.List32.nth xs i)) @@ e.at ], pc, bp)
        | Return, vs -> ([], [ SReturning vs @@ e.at ], pc, bp)
        | Call x, vs -> (vs, [ SInvoke (func frame.inst x) @@ e.at ], pc, bp)
        | CallIndirect x, (I32 i, _) :: vs ->
            let func = func_elem frame.inst (0l @@ e.at) i e.at in
            if type_ frame.inst x <> Func.type_of func then
              (vs, [ STrapping "indirect call type mismatch" @@ e.at ], pc, bp)
            else (vs, [ SInvoke func @@ e.at ], pc, bp)
        | Drop, v :: vs' -> (vs', [], pc, bp)
        | Select, (I32 0l, ve) :: v2 :: v1 :: vs' when is_concrete (simplify ve)
          ->
            (v2 :: vs', [], pc, bp)
        | Select, (I32 0l, ve) :: v2 :: v1 :: vs' ->
            let br = branch_on_cond false ve pc tree in
            (v2 :: vs', [], add_constraint ~neg:true ve pc, br :: bp)
        | Select, (I32 i, ex) :: v2 :: v1 :: vs' when is_concrete (simplify ex)
          ->
            (v1 :: vs', [], pc, bp)
        | Select, (I32 i, ex) :: v2 :: v1 :: vs' ->
            let br = branch_on_cond true ex pc tree in
            (v1 :: vs', [], add_constraint ex pc, br :: bp)
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
            let base = I64_convert.extend_i32_u i in
            (* overflow check *)
            let ptr = get_ptr (simplify sym_ptr) in
            try
              (if Option.is_some ptr then
               let low = I32Value.of_value (Option.get ptr) in
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
                | None -> Heap.load_value mem base offset ty
                | Some (sz, ext) -> Heap.load_packed sz ext mem base offset ty
              in
              ((v, e) :: vs', [], pc, bp)
            with
            | BugException (_, at, b) ->
                (vs', [ Interrupt (Bug b) @@ e.at ], pc, bp)
            | exn -> (vs', [ STrapping (memory_error e.at exn) @@ e.at ], pc, bp)
            )
        | Store { offset; sz; _ }, (v, ex) :: (I32 i, sym_ptr) :: vs' -> (
            let base = I64_convert.extend_i32_u i in
            let ptr = get_ptr (simplify sym_ptr) in
            try
              (if Option.is_some ptr then
               let low = I32Value.of_value (Option.get ptr) in
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
            | exn -> (vs', [ STrapping (memory_error e.at exn) @@ e.at ], pc, bp)
            )
        | MemorySize, vs ->
            let mem' = memory frame.inst (0l @@ e.at) in
            let v = I32 (Memory.size mem') in
            ((v, Value v) :: vs, [], pc, bp)
        | MemoryGrow, (I32 delta, _) :: vs' ->
            let mem' = memory frame.inst (0l @@ e.at) in
            let old_size = Memory.size mem' in
            let result =
              try
                Memory.grow mem' delta;
                old_size
              with
              | Memory.SizeOverflow | Memory.SizeLimit | Memory.OutOfMemory ->
                -1l
            in
            ((I32 result, Value (I32 result)) :: vs', [], pc, bp)
        | Const v, vs -> ((v.it, Value v.it) :: vs, [], pc, bp)
        | Test testop, v :: vs' -> (
            try (eval_testop v testop :: vs', [], pc, bp)
            with exn ->
              (vs', [ STrapping (numeric_error e.at exn) @@ e.at ], pc, bp))
        | Compare relop, v2 :: v1 :: vs' -> (
            try (eval_relop v1 v2 relop :: vs', [], pc, bp)
            with exn ->
              (vs', [ STrapping (numeric_error e.at exn) @@ e.at ], pc, bp))
        | Unary unop, v :: vs' -> (
            try (eval_unop v unop :: vs', [], pc, bp)
            with exn ->
              (vs', [ STrapping (numeric_error e.at exn) @@ e.at ], pc, bp))
        | Binary binop, v2 :: v1 :: vs' -> (
            try (eval_binop v1 v2 binop :: vs', [], pc, bp)
            with exn ->
              (vs', [ STrapping (numeric_error e.at exn) @@ e.at ], pc, bp))
        | Convert cvtop, v :: vs' -> (
            try (eval_cvtop cvtop v :: vs', [], pc, bp)
            with exn ->
              (vs', [ STrapping (numeric_error e.at exn) @@ e.at ], pc, bp))
        | Dup, v :: vs' -> (v :: v :: vs', [], pc, bp)
        | SymAssert, (I32 0l, ex) :: vs' ->
            debug ">>> Assert FAILED! Stopping...";
            (vs', [ Interrupt (AssFail pc) @@ e.at ], pc, bp)
        | SymAssert, (I32 i, ex) :: vs' when is_concrete (simplify ex) ->
            (vs', [], pc, bp)
        | SymAssert, (I32 i, ex) :: vs' -> (
            let formulas = add_constraint ~neg:true ex pc in
            match timed_check_sat (Formula.to_formulas formulas) with
            | None -> (vs', [], pc, bp)
            | Some m ->
                let binds = Encoding.lift m (Store.get_key_types store) in
                Store.update store binds;
                (vs', [ Interrupt (AssFail pc) @@ e.at ], pc, bp))
        | SymAssume, (I32 0l, ex) :: vs' when is_concrete (simplify ex) ->
            (vs', [ Interrupt (AsmFail pc) @@ e.at ], pc, bp)
        | SymAssume, (I32 0l, ex) :: vs' when not !Flags.smt_assume ->
            let br = branch_on_cond false ex pc tree in
            let pc' = add_constraint ~neg:true ex pc in
            (vs', [ Interrupt (AsmFail pc') @@ e.at ], pc', br :: bp)
        | SymAssume, (I32 0l, ex) :: vs' -> (
            debug
              (">>> Assumed false {line> "
              ^ Source.string_of_pos e.at.left
              ^ "}.");
            let pc' = add_constraint ex pc in
            let formulas = Formula.to_formulas pc' in
            match timed_check_sat formulas with
            | None ->
                let br = branch_on_cond false ex pc tree in
                let pc_fls = add_constraint ~neg:true ex pc in
                (vs', [ Interrupt (AsmFail pc') @@ e.at ], pc_fls, br :: bp)
            | Some m ->
                let tree', _ = Execution_tree.move_true !tree in
                tree := tree';
                let binds = Encoding.lift m (Store.get_key_types store) in
                Store.update store binds;
                Heap.update mem store;
                let f (_, s) = (Store.eval store s, s) in
                List.iter (fun a -> a := f !a) frame.locals;
                (List.map f vs', [], pc', bp))
        | SymAssume, (I32 i, ex) :: vs' when is_concrete (simplify ex) ->
            (vs', [], pc, bp)
        | SymAssume, (I32 i, ex) :: vs' ->
            debug ">>> Assume passed. Continuing execution...";
            let tree', _ = Execution_tree.move_true !tree in
            tree := tree';
            (vs', [], add_constraint ex pc, bp)
        | Symbolic (ty, b), (I32 i, _) :: vs' ->
            let base = I64_convert.extend_i32_u i in
            let x = Store.next store (Heap.load_string mem base) in
            let v = Store.get store x ty b in
            ((v, to_symbolic ty x) :: vs', [], pc, bp)
        | Boolop boolop, (v2, sv2) :: (v1, sv1) :: vs' -> (
            let sv2' = mk_relop sv2 (Values.type_of v2) in
            let v2' =
              Values.(value_of_bool (not (v2 = default_value (type_of v2))))
            in
            let sv1' = mk_relop sv1 (Values.type_of v1) in
            let v1' =
              Values.(value_of_bool (not (v1 = default_value (type_of v1))))
            in
            try
              let v3, sv3 = eval_binop (v1', sv1') (v2', sv2') boolop in
              ((v3, simplify sv3) :: vs', [], pc, bp)
            with exn ->
              (vs', [ STrapping (numeric_error e.at exn) @@ e.at ], pc, bp))
        | Alloc, (I32 a, sa) :: (I32 b, sb) :: vs' ->
            Hashtbl.add heap b a;
            ((I32 b, Ptr (I32 b)) :: vs', [], pc, bp)
        | Free, (I32 i, _) :: vs' ->
            let es' =
              if not (Hashtbl.mem heap i) then
                [ Interrupt (Bug InvalidFree) @@ e.at ]
              else (
                Hashtbl.remove heap i;
                [])
            in
            (vs', es', pc, bp)
        (* Deprecated *)
        | SymInt32 x, vs' -> Crash.error e.at "SymInt32: deprecated!"
        | SymInt64 x, vs' -> Crash.error e.at "SymInt64: deprecated!"
        | SymFloat32 x, vs' -> Crash.error e.at "SymFloat32: deprecated!"
        | SymFloat64 x, vs' -> Crash.error e.at "SymFloat64: deprecated!"
        | GetSymInt32 x, vs' ->
            let v =
              try Store.find store x
              with Not_found ->
                Crash.error e.at "Symbolic variable was not in store."
            in
            ((v, Symvalue.Symbolic (SymInt32, x)) :: vs', [], pc, bp)
        | GetSymInt64 x, vs' ->
            let v =
              try Store.find store x
              with Not_found ->
                Crash.error e.at "Symbolic variable was not in store."
            in
            ((v, Symvalue.Symbolic (SymInt64, x)) :: vs', [], pc, bp)
        | GetSymFloat32 x, vs' ->
            let v =
              try Store.find store x
              with Not_found ->
                Crash.error e.at "Symbolic variable was not in store."
            in
            ((v, Symvalue.Symbolic (SymFloat32, x)) :: vs', [], pc, bp)
        | GetSymFloat64 x, vs' ->
            let v =
              try Store.find store x
              with Not_found ->
                Crash.error e.at "Symbolic variable was not in store."
            in
            ((v, Symvalue.Symbolic (SymFloat64, x)) :: vs', [], pc, bp)
        | TernaryOp, (I32 r2, s_r2) :: (I32 r1, s_r1) :: (I32 c, s_c) :: vs' ->
            let r = I32 (if c = 0l then r2 else r1) in
            let s_c' = to_constraint (simplify s_c) in
            let v, pc' =
              match s_c' with
              | None -> ((r, if c = 0l then s_r2 else s_r1), pc)
              | Some s ->
                  let x = Store.next store "__ternary" in
                  Store.add store x r;
                  let s_x = to_symbolic I32Type x in
                  let t_eq = I32Relop (I32Eq, s_x, s_r1) in
                  let t_imp = I32Binop (I32Or, negate_relop s, t_eq) in
                  let f_eq = I32Relop (I32Eq, s_x, s_r2) in
                  let f_imp = I32Binop (I32Or, s, f_eq) in
                  let cond = I32Binop (I32And, t_imp, f_imp) in
                  ((r, s_x), I32Relop (I32Ne, cond, Value (I32 0l)) :: pc)
            in
            (v :: vs', [], pc', bp)
        | PrintStack, vs' ->
            debug ("Stack dump: " ^ string_of_sym_value vs');
            (vs', [], pc, bp)
        | PrintMemory, vs' ->
            debug ("Memory dump:\n" ^ Heap.to_string mem);
            (vs', [], pc, bp)
        | PrintBtree, vs' ->
            Printf.printf "B TREE STATE: \n\n";
            Btree.print_b_tree mem;
            (vs', [], pc, bp)
        | CompareExpr, (v1, ex1) :: (v2, ex2) :: vs' ->
            let res =
              match (ex1, ex2) with
              | Symbolic (SymInt32, x), Symbolic (SymInt32, y) ->
                  if x = y then (I32 1l, Symvalue.I32Relop (I32Eq, ex1, ex2))
                  else (I32 0l, Symvalue.I32Relop (I32Ne, ex1, ex2))
              | _, _ -> eval_relop (v1, ex1) (v2, ex2) (Values.I32 Ast.I32Op.Eq)
            in
            (res :: vs', [], pc, bp)
        | IsSymbolic, (I32 n, _) :: (I32 i, _) :: vs' ->
            let base = I64_convert.extend_i32_u i in
            let _, v = Heap.load_bytes mem base (Int32.to_int n) in
            let result = I32 (match v with Value _ -> 0l | _ -> 1l) in
            ((result, Value result) :: vs', [], pc, bp)
        | SetPriority, _ :: _ :: _ :: vs' -> (vs', [], pc, bp)
        | PopPriority, _ :: vs' -> (vs', [], pc, bp)
        | _ -> Crash.error e.at "missing or ill-typed operand on stack")
    | STrapping msg, vs -> assert false
    | Interrupt i, vs -> assert false
    | SReturning vs', vs -> Crash.error e.at "undefined frame"
    | SBreaking (k, vs'), vs -> Crash.error e.at "undefined label"
    | SLabel (n, es0, (vs', [])), vs -> (vs' @ vs, [], pc, bp)
    | SLabel (n, es0, (vs', { it = Interrupt i; at } :: es')), vs ->
        ( vs,
          [ Interrupt i @@ at ] @ [ SLabel (n, es0, (vs', es')) @@ e.at ],
          pc,
          bp )
    | SLabel (n, es0, (vs', { it = STrapping msg; at } :: es')), vs ->
        (vs, [ STrapping msg @@ at ], pc, bp)
    | SLabel (n, es0, (vs', { it = SReturning vs0; at } :: es')), vs ->
        (vs, [ SReturning vs0 @@ at ], pc, bp)
    | SLabel (n, es0, (vs', { it = SBreaking (0l, vs0); at } :: es')), vs ->
        (take n vs0 e.at @ vs, List.map plain es0, pc, bp)
    | SLabel (n, es0, (vs', { it = SBreaking (k, vs0); at } :: es')), vs ->
        (vs, [ SBreaking (Int32.sub k 1l, vs0) @@ at ], pc, bp)
    | SLabel (n, es0, code'), vs ->
        let c' = step { c with code = code' } in
        (vs, [ SLabel (n, es0, c'.code) @@ e.at ], c'.pc, c'.bp)
    | SFrame (n, frame', (vs', [])), vs -> (vs' @ vs, [], pc, bp)
    | SFrame (n, frame', (vs', { it = Interrupt i; at } :: es')), vs ->
        ( vs,
          [ Interrupt i @@ at ] @ [ SFrame (n, frame', (vs', es')) @@ e.at ],
          pc,
          bp )
    | SFrame (n, frame', (vs', { it = STrapping msg; at } :: es')), vs ->
        (vs, [ STrapping msg @@ at ], pc, bp)
    | SFrame (n, frame', (vs', { it = SReturning vs0; at } :: es')), vs ->
        (take n vs0 e.at @ vs, [], pc, bp)
    | SFrame (n, frame', code'), vs ->
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
        (vs, [ SFrame (n, c'.frame, c'.code) @@ e.at ], c'.pc, c'.bp)
    | SInvoke func, vs when c.budget = 0 ->
        Exhaustion.error e.at "call stack exhausted"
    | SInvoke func, vs -> (
        let symbolic_arg t =
          let x = Store.next store "arg" in
          let v = Store.get store x t false in
          (v, to_symbolic t x)
        in
        let (FuncType (ins, out)) = Func.type_of func in
        let n = List.length ins in
        let vs =
          if n > 0 && List.length vs = 0 then
            List.map (fun t -> symbolic_arg t) ins
          else vs
        in
        let args, vs' = (take n vs e.at, drop n vs e.at) in
        match func with
        | Func.AstFunc (t, inst', f) ->
            let locals' =
              List.map
                (fun v -> (v, Symvalue.Value v))
                (List.map default_value f.it.locals)
            in
            let locals'' = List.rev args @ locals' in
            let code' = ([], [ SPlain (Block (out, f.it.body)) @@ f.at ]) in
            let frame' = { inst = !inst'; locals = List.map ref locals'' } in
            (vs', [ SFrame (List.length out, frame', code') @@ e.at ], pc, bp)
        | Func.HostFunc (t, f) -> failwith "HostFunc error")
  in
  let e' =
    step_cnt := !step_cnt + 1;
    if (not (!Flags.inst_limit = -1)) && !step_cnt >= !Flags.inst_limit then
      [ Interrupt IntLimit @@ e.at ]
    else []
  in
  { c with code = (vs', e' @ es' @ List.tl es); pc = pc'; bp = bp' }

let get_reason error : string =
  let type_str, r = error in
  let region_str =
    Source.string_of_pos r.left
    ^ if r.right = r.left then "" else "-" ^ string_of_pos r.right
  in
  "{" ^ "\"type\" : \"" ^ type_str ^ "\", " ^ "\"line\" : \"" ^ region_str
  ^ "\"" ^ "}"

let write_test_case out_dir test_data is_witness cnt : unit =
  if not (test_data = "[]") then
    let i = cnt () in
    let filename =
      if is_witness then Printf.sprintf "%s/witness_%05d.json" out_dir i
      else Printf.sprintf "%s/test_%05d.json" out_dir i
    in
    Io.save_file filename test_data

let write_report spec reason witness loop_time : unit =
  let report_str =
    "{" ^ "\"specification\": " ^ string_of_bool spec ^ ", " ^ "\"reason\" : "
    ^ reason ^ ", " ^ "\"loop_time\" : \"" ^ string_of_float loop_time ^ "\", "
    ^ "\"solver_time\" : \""
    ^ string_of_float !solver_time
    ^ "\", " ^ "\"paths_explored\" : " ^ string_of_int !iterations ^ ", "
    ^ "\"solver_counter\" : " ^ string_of_int !solver_cnt ^ ", "
    ^ "\"instruction_counter\" : " ^ string_of_int !step_cnt ^ "}"
  in
  Io.save_file (Filename.concat !Flags.output "report.json") report_str

let update_config c model glob code mem =
  let binds = Encoding.lift model (Store.get_key_types c.store) in
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
    let skip = ref false in
    let rec loop c =
      let rec eval (c : config) : config =
        match c.code with
        | vs, [] -> c
        | vs, { it = STrapping msg; at } :: _ -> Trap.error at msg
        | vs, { it = Interrupt (AsmFail pc); at } :: _ ->
            skip := true;
            iterations := !iterations - 1;
            { c with code = ([], []) }
        | vs, { it = Interrupt i; at } :: es -> c
        | vs, es ->
            let c' = step c in
            List.iter (fun pc -> if not (pc = []) then L.push pc wl) c'.bp;
            eval { c' with bp = [] }
      in
      skip := false;
      iterations := !iterations + 1;
      let { code = _, es; store; bp; _ } = eval c in
      List.iter (fun pc -> if not (pc = []) then L.push pc wl) bp;
      let err =
        match es with
        | { it = Interrupt i; at } :: _ -> Some (i, at)
        | _ -> None
      in
      if not !skip then
        write_test_case test_suite
          Store.(to_json (to_list store))
          (Option.is_some err) cntr;
      if Option.is_some err then false
      else if L.is_empty wl then true
      else
        let rec find_sat_pc pcs =
          if L.is_empty pcs then None
          else
            match timed_check_sat (Formula.to_formulas (L.pop pcs)) with
            | None -> find_sat_pc pcs
            | Some m -> Some m
        in
        match find_sat_pc wl with
        | None -> true
        | Some m -> loop (update_config c m glob0 code0 mem0)
    in
    loop_start := Sys.time ();
    let spec = loop c in
    write_report spec "{}" "[]" (Sys.time () -. !loop_start)
end

module RandArray : Work_list = struct
  type 'a t = 'a BatDynArray.t

  exception Empty

  let create () = BatDynArray.create ()
  let is_empty a = BatDynArray.empty a
  let push v a = BatDynArray.add a v

  let pop a =
    Random.self_init ();
    BatDynArray.get a (Random.int (BatDynArray.length a))
end

module DFS = Guided_search (Stack)
module BFS = Guided_search (Queue)
module RND = Guided_search (RandArray)

let set_timeout (time_limit : int) : unit =
  let alarm_handler i : unit =
    Encoding.interrupt_z3 ();
    let loop_time = Sys.time () -. !loop_start in
    write_report true "{}" "[]" loop_time;
    exit 0
  in
  if time_limit > 0 then (
    Sys.(set_signal sigalrm (Signal_handle alarm_handler));
    ignore (Unix.alarm time_limit))

let main (func : func_inst) (vs : sym_value list) (inst : module_inst) =
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
            (Int32.of_int i, (v, Symvalue.Value v)))
          inst.globals));
  let c =
    config empty_module_inst (List.rev vs)
      [ SInvoke func @@ at ]
      inst.sym_memory glob (ref head)
  in
  let f =
    match parse_policy !Flags.policy with
    | None -> Crash.error at ("invalid search policy '" ^ !Flags.policy ^ "'")
    | Some Depth -> DFS.invoke
    | Some Breadth -> BFS.invoke
    | Some Random -> RND.invoke
  in
  f c test_suite

let i32 (v : value) at =
  match v with
  | I32 i -> i
  | _ -> Crash.error at "type error: i32 value expected"

let create_func (inst : module_inst) (f : func) : func_inst =
  Func.alloc (type_ inst f.it.ftype) (ref inst) f

let create_table (inst : module_inst) (tab : table) : table_inst =
  let { ttype } = tab.it in
  Table.alloc ttype

let create_memory (inst : module_inst) (mem : memory) : memory_inst =
  let { mtype } = mem.it in
  Memory.alloc mtype

let create_global (inst : module_inst) (glob : global) : global_inst =
  let { gtype; value } = glob.it in
  let v = Eval.eval_const inst value in
  Global.alloc gtype v

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
  | Func.AstFunc (_, inst_ref, _) -> inst_ref := inst
  | _ -> assert false

let init_table (inst : module_inst) (seg : table_segment) =
  let { index; offset = const; init } = seg.it in
  let tab = table inst index in
  let offset = i32 (Eval.eval_const inst const) const.at in
  let end_ = Int32.(add offset (of_int (List.length init))) in
  let bound = Table.size tab in
  if I32.lt_u bound end_ || I32.lt_u end_ offset then
    Link.error seg.at "elements segment does not fit table";
  fun () ->
    Table.blit tab offset (List.map (fun x -> FuncElem (func inst x)) init)

let init_memory (inst : module_inst) (seg : memory_segment) =
  let { index; offset = const; init } = seg.it in
  let mem = memory inst index in
  let sym_mem = inst.sym_memory in
  let offset' = i32 (Eval.eval_const inst const) const.at in
  let offset = I64_convert.extend_i32_u offset' in
  let end_ = Int64.(add offset (of_int (String.length init))) in
  let bound = Memory.bound mem in
  if I64.lt_u bound end_ || I64.lt_u end_ offset then
    Link.error seg.at "data segment does not fit memory";
  fun () -> Heap.store_bytes sym_mem offset init

let add_import (m : module_) (ext : extern) (im : import) (inst : module_inst) :
    module_inst =
  if not (match_extern_type (extern_type_of ext) (import_type m im)) then
    Link.error im.at "incompatible import type";
  match ext with
  | ExternFunc func -> { inst with funcs = func :: inst.funcs }
  | ExternTable tab -> { inst with tables = tab :: inst.tables }
  | ExternMemory mem -> { inst with memories = mem :: inst.memories }
  | ExternGlobal glob -> { inst with globals = glob :: inst.globals }

let init (m : module_) (exts : extern list) : module_inst =
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
  let init_datas = List.map (init_memory inst) data in
  List.iter (fun f -> f ()) init_elems;
  List.iter (fun f -> f ()) init_datas;
  Lib.Option.app (fun x -> ignore (main (func inst x) [] inst)) start;
  inst
