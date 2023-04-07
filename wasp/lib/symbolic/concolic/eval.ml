open Evaluations
open Common
open Encoding
open Expression
open Types
open Interpreter.Ast
open Interpreter.Source
open Interpreter.Instance

let memory_error at = function
  | Heap.InvalidAddress a ->
      Int64.to_string a ^ ":address not found in hashtable"
  | Heap.Bounds -> "out of bounds memory access"
  | Interpreter.Memory.SizeOverflow -> "memory size overflow"
  | Interpreter.Memory.SizeLimit -> "memory size limit reached"
  | Interpreter.Memory.Type -> Crash.error at "type mismatch at memory access"
  | exn -> raise exn

type policy = Random | Depth | Breadth
type interruption = Limit | Failure of Formula.t | Bug of Bug.bug
type value = Num.t * Expression.t
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
  | Restart of Formula.t

type config = {
  frame : frame;
  glob : value Globals.t;
  code : code;
  mem : Heap.t;
  store : Store.t;
  heap : Chunktable.t;
  pc : Formula.t;
  bp : bp list;
  tree : tree ref;
  budget : int;
  call_stack : region Stack.t;
}

and tree = config ref Execution_tree.t ref
and bp = Branchpoint of Formula.t * tree | Checkpoint of config ref

let frame inst locals = { inst; locals }

let clone_frame (f : frame) : frame =
  frame f.inst (List.map (fun l -> ref !l) f.locals)

let rec clone_admin_instr e =
  let it =
    match e.it with
    | Label (n, es0, (vs, es)) ->
        Label (n, es0, (vs, List.map clone_admin_instr es))
    | Frame (n, frame, (vs, es)) ->
        Frame (n, clone_frame frame, (vs, List.map clone_admin_instr es))
    | _ -> e.it
  in
  { it; at = e.at }

let clone (c : config) : Heap.t * config =
  let vs, es = c.code in
  let frame = clone_frame c.frame
  and glob = Globals.copy c.glob
  and code = (vs, List.map clone_admin_instr es)
  and mem, mem' = Heap.clone c.mem
  and store = Store.copy c.store
  and heap = Chunktable.copy c.heap
  and pc = c.pc
  and bp = []
  and tree = ref !(c.tree)
  and budget = c.budget
  and call_stack = Stack.copy c.call_stack in
  ( mem',
    { frame; glob; code; mem; store; heap; pc; bp; tree; budget; call_stack } )

let config inst vs es mem glob tree =
  {
    frame = frame inst [];
    glob;
    code = (vs, es);
    mem;
    store = Store.create [];
    heap = Chunktable.create ();
    pc = Formula.create ();
    bp = [];
    tree;
    budget = Interpreter.Flags.budget;
    call_stack = Stack.create ();
  }

exception BugException of config * region * Bug.bug

let head = ref Execution_tree.(Node (None, None, ref Leaf, ref Leaf))
let step_cnt = ref 0
let iterations = ref 0
let loop_start = ref 0.
let solver = Batch.create ()
let debug str = if !Interpreter.Flags.trace then print_endline str

let parse_policy (p : string) : policy option =
  match p with
  | "random" -> Some Random
  | "depth" -> Some Depth
  | "breadth" -> Some Breadth
  | _ -> None

let string_of_interruption : interruption -> string = function
  | Limit -> "Analysis Limit"
  | Failure _ -> "Assertion Failure"
  | Bug b -> Bug.string_of_bug b

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
  if to_branch then Some (Formula.add_constraint ~neg:bval c pc) else None

module type Checkpoint = sig
  val is_checkpoint : config -> bool
end

module NoCheckpoint : Checkpoint = struct
  let is_checkpoint (_ : config) : bool = false
end

module FuncCheckpoint : Checkpoint = struct
  let visited = Hashtbl.create Interpreter.Flags.hashtbl_default_size

  let is_checkpoint (c : config) : bool =
    let func = Stack.top c.call_stack in
    if Hashtbl.mem visited func then false
    else (
      Hashtbl.add visited func true;
      Execution_tree.can_branch !(c.tree))
end

module RandCheckpoint : Checkpoint = struct
  let is_checkpoint (c : config) : bool =
    Execution_tree.can_branch !(c.tree) && Random.bool ()
end

module DepthCheckpoint : Checkpoint = struct
  let count = Counter.create ()

  let is_checkpoint (c : config) : bool =
    let size_pc = Formula.length c.pc in
    Execution_tree.can_branch !(c.tree)
    && size_pc mod 10 = 0
    && Counter.get_and_inc count size_pc < 5
end

module type Stepper = sig
  val step : config -> config
end

module ConcolicStepper (C : Checkpoint) : Stepper = struct
  let rec step (c : config) : config =
    let {
      frame;
      glob;
      code = vs, es;
      mem;
      store;
      heap;
      pc;
      bp;
      tree;
      call_stack;
      _;
    } =
      c
    in
    let e = List.hd es in
    let vs', es', mem', pc', bp' =
      match (e.it, vs) with
      | Plain e', vs -> (
          match (e', vs) with
          | Unreachable, vs ->
              (vs, [ Trapping "unreachable executed" @@ e.at ], mem, pc, bp)
          | Nop, vs -> (vs, [], mem, pc, bp)
          | Block (ts, es'), vs ->
              let es' =
                [ Label (List.length ts, [], ([], List.map plain es')) @@ e.at ]
              in
              (vs, es', mem, pc, bp)
          | Loop (ts, es'), vs ->
              ( vs,
                [ Label (0, [ e' @@ e.at ], ([], List.map plain es')) @@ e.at ],
                mem,
                pc,
                bp )
          | If (ts, es1, es2), (I32 i, ex) :: vs' when is_concrete (simplify ex)
            ->
              if i = 0l then
                (vs', [ Plain (Block (ts, es2)) @@ e.at ], mem, pc, bp)
              else (vs', [ Plain (Block (ts, es1)) @@ e.at ], mem, pc, bp)
          | If (ts, es1, es2), (I32 i, ex) :: vs' ->
              let b, es1', es2' =
                ( i <> 0l,
                  [ Plain (Block (ts, es1)) @@ e.at ],
                  [ Plain (Block (ts, es2)) @@ e.at ] )
              in
              let mem', bp =
                let pc' = Formula.add_constraint ~neg:b ex pc in
                if not (C.is_checkpoint c) then (mem, bp)
                else
                  let mem, c' = clone c in
                  ignore (branch_on_cond (not b) ex c'.pc c'.tree);
                  let es' = (if not b then es1' else es2') @ List.tl es in
                  let cp = ref { c' with code = (vs', es'); pc = pc' } in
                  Execution_tree.update_node !(c'.tree) cp;
                  (mem, Checkpoint cp :: bp)
              in
              let bp' =
                Base.Option.fold ~init:bp
                  ~f:(fun br pc -> Branchpoint (pc, !tree) :: br)
                  (branch_on_cond b ex pc tree)
              in
              let pc' = Formula.add_constraint ~neg:(not b) ex pc in
              (vs', (if b then es1' else es2'), mem', pc', bp')
          | Br x, vs -> ([], [ Breaking (x.it, vs) @@ e.at ], mem, pc, bp)
          | BrIf x, (I32 i, ex) :: vs' when is_concrete (simplify ex) ->
              if i = 0l then (vs', [], mem, pc, bp)
              else (vs', [ Plain (Br x) @@ e.at ], mem, pc, bp)
          | BrIf x, (I32 i, ex) :: vs' ->
              let b, es1', es2' = (i <> 0l, [ Plain (Br x) @@ e.at ], []) in
              let mem', bp =
                let pc' = Formula.add_constraint ~neg:b ex pc in
                if not (C.is_checkpoint c) then (mem, bp)
                else
                  let mem, c' = clone c in
                  ignore (branch_on_cond (not b) ex c'.pc c'.tree);
                  let es' = (if not b then es1' else es2') @ List.tl es in
                  let cp = ref { c' with code = (vs', es'); pc = pc' } in
                  Execution_tree.update_node !(c'.tree) cp;
                  (mem, Checkpoint cp :: bp)
              in
              let bp' =
                Base.Option.fold ~init:bp
                  ~f:(fun br pc -> Branchpoint (pc, !tree) :: br)
                  (branch_on_cond b ex pc tree)
              in
              let pc' = Formula.add_constraint ~neg:(not b) ex pc in
              (vs', (if b then es1' else es2'), mem', pc', bp')
          | BrTable (xs, x), (I32 i, _) :: vs'
            when Interpreter.I32.ge_u i (Interpreter.Lib.List32.length xs) ->
              (vs', [ Plain (Br x) @@ e.at ], mem, pc, bp)
          | BrTable (xs, x), (I32 i, _) :: vs' ->
              ( vs',
                [ Plain (Br (Interpreter.Lib.List32.nth xs i)) @@ e.at ],
                mem,
                pc,
                bp )
          | Return, vs -> ([], [ Returning vs @@ e.at ], mem, pc, bp)
          | Call x, vs ->
              (vs, [ Invoke (func frame.inst x) @@ e.at ], mem, pc, bp)
          | CallIndirect x, (I32 i, _) :: vs ->
              let func = func_elem frame.inst (0l @@ e.at) i e.at in
              if type_ frame.inst x <> Interpreter.Func.type_of func then
                ( vs,
                  [ Trapping "indirect call type mismatch" @@ e.at ],
                  mem,
                  pc,
                  bp )
              else (vs, [ Invoke func @@ e.at ], mem, pc, bp)
          | Drop, v :: vs' -> (vs', [], mem, pc, bp)
          | Select, (I32 i, ve) :: v2 :: v1 :: vs'
            when is_concrete (simplify ve) ->
              if i = 0l then (v2 :: vs', [], mem, pc, bp)
              else (v1 :: vs', [], mem, pc, bp)
          | Select, (I32 i, ve) :: v2 :: v1 :: vs' ->
              let b, vs1, vs2 = (i <> 0l, v1 :: vs', v2 :: vs') in
              let mem', bp =
                let pc' = Formula.add_constraint ~neg:b ve pc in
                if not (C.is_checkpoint c) then (mem, bp)
                else
                  let mem, c' = clone c in
                  ignore (branch_on_cond (not b) ve c'.pc c'.tree);
                  let vs' = if not b then vs1 else vs2 in
                  let cp = ref { c' with code = (vs', List.tl es); pc = pc' } in
                  Execution_tree.update_node !(c'.tree) cp;
                  (mem, Checkpoint cp :: bp)
              in
              let bp' =
                Base.Option.fold ~init:bp
                  ~f:(fun br pc -> Branchpoint (pc, !tree) :: br)
                  (branch_on_cond b ve pc tree)
              in
              let pc' = Formula.add_constraint ~neg:(not b) ve pc in
              ((if b then vs1 else vs2), [], mem', pc', bp')
          | LocalGet x, vs -> (!(local frame x) :: vs, [], mem, pc, bp)
          | LocalSet x, (v, ex) :: vs' ->
              local frame x := (v, simplify ex);
              (vs', [], mem, pc, bp)
          | LocalTee x, (v, ex) :: vs' ->
              local frame x := (v, simplify ex);
              (!(local frame x) :: vs', [], mem, pc, bp)
          | GlobalGet x, vs -> (Globals.find glob x.it :: vs, [], mem, pc, bp)
          | GlobalSet x, v :: vs' ->
              Globals.add glob x.it v;
              (vs', [], mem, pc, bp)
          | Load { offset; ty; sz; _ }, (I32 i, sym_ptr) :: vs' -> (
              try
                let base = Interpreter.I64_convert.extend_i32_u i in
                (* overflow check *)
                let ptr = concretize_base_ptr (simplify sym_ptr) in
                match
                  Option.bind ptr (fun bp ->
                      Chunktable.check_access heap bp (I32 i) offset)
                with
                | Some b -> (vs', [ Interrupt (Bug b) @@ e.at ], mem, pc, bp)
                | None ->
                    let v, e =
                      match sz with
                      | None ->
                          Heap.load_value mem base offset
                            (Evaluations.to_num_type ty)
                      | Some (sz, ext) ->
                          Heap.load_packed sz ext mem base offset
                            (Evaluations.to_num_type ty)
                    in
                    ((v, e) :: vs', [], mem, pc, bp)
              with exn ->
                (vs', [ Trapping (memory_error e.at exn) @@ e.at ], mem, pc, bp)
              )
          | Store { offset; sz; _ }, (v, ex) :: (I32 i, sym_ptr) :: vs' -> (
              try
                let base = Interpreter.I64_convert.extend_i32_u i in
                let ptr = concretize_base_ptr (simplify sym_ptr) in
                match
                  Option.bind ptr (fun bp ->
                      Chunktable.check_access heap bp (I32 i) offset)
                with
                | Some b -> (vs', [ Interrupt (Bug b) @@ e.at ], mem, pc, bp)
                | None ->
                    (match sz with
                    | None -> Heap.store_value mem base offset (v, simplify ex)
                    | Some sz ->
                        Heap.store_packed sz mem base offset (v, simplify ex));
                    (vs', [], mem, pc, bp)
              with exn ->
                (vs', [ Trapping (memory_error e.at exn) @@ e.at ], mem, pc, bp)
              )
          | MemorySize, vs ->
              let mem' = memory frame.inst (0l @@ e.at) in
              let v : Num.t = I32 (Interpreter.Memory.size mem') in
              ((v, Val (Num v)) :: vs, [], mem, pc, bp)
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
              ((I32 result, Val (Num (I32 result))) :: vs', [], mem, pc, bp)
          | Const v, vs ->
              let v' = Evaluations.of_value v.it in
              ((v', Val (Num v')) :: vs, [], mem, pc, bp)
          | Test testop, v :: vs' -> (
              try (eval_testop v testop :: vs', [], mem, pc, bp)
              with exn ->
                (vs', [ Trapping (numeric_error e.at exn) @@ e.at ], mem, pc, bp)
              )
          | Compare relop, v2 :: v1 :: vs' -> (
              try (eval_relop v1 v2 relop :: vs', [], mem, pc, bp)
              with exn ->
                (vs', [ Trapping (numeric_error e.at exn) @@ e.at ], mem, pc, bp)
              )
          | Unary unop, v :: vs' -> (
              try (eval_unop v unop :: vs', [], mem, pc, bp)
              with exn ->
                (vs', [ Trapping (numeric_error e.at exn) @@ e.at ], mem, pc, bp)
              )
          | Binary binop, v2 :: v1 :: vs' -> (
              try (eval_binop v1 v2 binop :: vs', [], mem, pc, bp)
              with exn ->
                (vs', [ Trapping (numeric_error e.at exn) @@ e.at ], mem, pc, bp)
              )
          | Convert cvtop, v :: vs' -> (
              try (eval_cvtop cvtop v :: vs', [], mem, pc, bp)
              with exn ->
                (vs', [ Trapping (numeric_error e.at exn) @@ e.at ], mem, pc, bp)
              )
          | Dup, v :: vs' -> (v :: v :: vs', [], mem, pc, bp)
          | SymAssert, (I32 0l, ex) :: vs' ->
              debug ">>> Assert FAILED! Stopping...";
              (vs', [ Interrupt (Failure pc) @@ e.at ], mem, pc, bp)
          | SymAssert, (I32 i, ex) :: vs' when is_concrete (simplify ex) ->
              (vs', [], mem, pc, bp)
          | SymAssert, (I32 i, ex) :: vs' ->
              let formulas = Formula.add_constraint ~neg:true ex pc in
              if not (Batch.check_formulas solver [ formulas ]) then
                (vs', [], mem, pc, bp)
              else
                let binds =
                  Batch.value_binds solver (Store.get_key_types store)
                in
                Store.update store binds;
                (vs', [ Interrupt (Failure pc) @@ e.at ], mem, pc, bp)
          | SymAssume, (I32 i, ex) :: vs' when is_concrete (simplify ex) ->
              let unsat = Formula.False in
              if i = 0l then (vs', [ Restart unsat @@ e.at ], mem, pc, bp)
              else (vs', [], mem, pc, bp)
          | SymAssume, (I32 i, ex) :: vs' ->
              if i = 0l then
                ( vs',
                  [ Restart (Formula.add_constraint ex pc) @@ e.at ],
                  mem,
                  pc,
                  bp )
              else (
                debug ">>> Assume passed. Continuing execution...";
                let tree', _ = Execution_tree.move_true !tree in
                tree := tree';
                (vs', [], mem, Formula.add_constraint ex pc, bp))
          | Symbolic (ty, b), (I32 i, _) :: vs' ->
              let base = Interpreter.I64_convert.extend_i32_u i in
              let symbol = if i = 0l then "x" else Heap.load_string mem base in
              let x = Store.next store symbol in
              let ty' = Evaluations.to_num_type ty in
              let v = Store.get store x ty' b in
              ((v, symbolic ty' x) :: vs', [], mem, pc, bp)
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
                ((v3, simplify sv3) :: vs', [], mem, pc, bp)
              with exn ->
                (vs', [ Trapping (numeric_error e.at exn) @@ e.at ], mem, pc, bp)
              )
          | Alloc, (I32 a, sa) :: (I32 b, sb) :: vs' ->
              Hashtbl.add heap b a;
              ((I32 b, SymPtr (b, Val (Num (I32 0l)))) :: vs', [], mem, pc, bp)
          | Free, (I32 i, _) :: vs' ->
              let es' =
                if not (Hashtbl.mem heap i) then
                  [ Interrupt (Bug Bug.InvalidFree) @@ e.at ]
                else (
                  Hashtbl.remove heap i;
                  [])
              in
              (vs', es', mem, pc, bp)
          | GetSymInt32 x, vs' ->
              let v =
                try Store.find store x
                with Not_found ->
                  Crash.error e.at "Symbolic variable was not in store."
              in
              ((v, symbolic `I32Type x) :: vs', [], mem, pc, bp)
          | GetSymInt64 x, vs' ->
              let v =
                try Store.find store x
                with Not_found ->
                  Crash.error e.at "Symbolic variable was not in store."
              in
              ((v, symbolic `I64Type x) :: vs', [], mem, pc, bp)
          | GetSymFloat32 x, vs' ->
              let v =
                try Store.find store x
                with Not_found ->
                  Crash.error e.at "Symbolic variable was not in store."
              in
              ((v, symbolic `F32Type x) :: vs', [], mem, pc, bp)
          | GetSymFloat64 x, vs' ->
              let v =
                try Store.find store x
                with Not_found ->
                  Crash.error e.at "Symbolic variable was not in store."
              in
              ((v, symbolic `F64Type x) :: vs', [], mem, pc, bp)
          | TernaryOp, (I32 r2, s_r2) :: (I32 r1, s_r1) :: (I32 c, s_c) :: vs'
            ->
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
                    ( (r, s_x),
                      Formula.add_constraint
                        (Relop (I32 I32.Ne, cond, Val (Num (I32 0l))))
                        pc )
              in
              (v :: vs', [], mem, pc', bp)
          | PrintStack, vs' ->
              debug
                (Interpreter.Source.string_of_pos e.at.left
                ^ ":VS:\n"
                ^ Expression.string_of_values vs');
              (vs', [], mem, pc, bp)
          | PrintPC, vs' ->
              debug
                (Interpreter.Source.string_of_pos e.at.left
                ^ ":PC: "
                ^ Formula.(pp_to_string pc));
              (vs', [], mem, pc, bp)
          | PrintMemory, vs' ->
              debug ("Mem:\n" ^ Heap.to_string mem);
              (vs', [], mem, pc, bp)
          | PrintBtree, vs' ->
              Printf.printf "B TREE STATE: \n\n";
              (* Btree.print_b_tree mem; *)
              (vs', [], mem, pc, bp)
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
              (res :: vs', [], mem, pc, bp)
          | IsSymbolic, (I32 n, _) :: (I32 i, _) :: vs' ->
              let base = Interpreter.I64_convert.extend_i32_u i in
              let _, v = Heap.load_bytes mem base (Int32.to_int n) in
              let result : Num.t = I32 (match v with Val _ -> 0l | _ -> 1l) in
              ((result, Val (Num result)) :: vs', [], mem, pc, bp)
          | SetPriority, _ :: _ :: _ :: vs' -> (vs', [], mem, pc, bp)
          | PopPriority, _ :: vs' -> (vs', [], mem, pc, bp)
          | _ -> Crash.error e.at "missing or ill-typed operand on stack")
      | Trapping msg, vs -> assert false
      | Interrupt i, vs -> assert false
      | Restart pc, vs -> assert false
      | Returning vs', vs -> Crash.error e.at "undefined frame"
      | Breaking (k, vs'), vs -> Crash.error e.at "undefined label"
      | Label (n, es0, (vs', [])), vs -> (vs' @ vs, [], mem, pc, bp)
      | Label (n, es0, (vs', { it = Restart pc'; at } :: es')), vs ->
          ( vs,
            [ Restart pc' @@ at; Label (n, es0, (vs', es')) @@ e.at ],
            mem,
            pc,
            bp )
      | Label (n, es0, (vs', { it = Interrupt i; at } :: es')), vs ->
          ( vs,
            [ Interrupt i @@ at; Label (n, es0, (vs', es')) @@ e.at ],
            mem,
            pc,
            bp )
      | Label (n, es0, (vs', { it = Trapping msg; at } :: es')), vs ->
          (vs, [ Trapping msg @@ at ], mem, pc, bp)
      | Label (n, es0, (vs', { it = Returning vs0; at } :: es')), vs ->
          (vs, [ Returning vs0 @@ at ], mem, pc, bp)
      | Label (n, es0, (vs', { it = Breaking (0l, vs0); at } :: es')), vs ->
          (take n vs0 e.at @ vs, List.map plain es0, mem, pc, bp)
      | Label (n, es0, (vs', { it = Breaking (k, vs0); at } :: es')), vs ->
          (vs, [ Breaking (Int32.sub k 1l, vs0) @@ at ], mem, pc, bp)
      | Label (n, es0, code'), vs ->
          let c' = step { c with code = code' } in
          List.iter
            (fun bp ->
              match bp with
              | Branchpoint _ -> ()
              | Checkpoint cp ->
                  let es' = (Label (n, es0, !cp.code) @@ e.at) :: List.tl es in
                  cp := { !cp with code = (vs, es') })
            c'.bp;
          (vs, [ Label (n, es0, c'.code) @@ e.at ], c'.mem, c'.pc, c'.bp)
      | Frame (n, frame', (vs', [])), vs ->
          ignore (Stack.pop call_stack);
          (vs' @ vs, [], mem, pc, bp)
      | Frame (n, frame', (vs', { it = Restart pc'; at } :: es')), vs ->
          ( vs,
            [ Restart pc' @@ at; Frame (n, frame', (vs', es')) @@ e.at ],
            mem,
            pc,
            bp )
      | Frame (n, frame', (vs', { it = Interrupt i; at } :: es')), vs ->
          ( vs,
            [ Interrupt i @@ at; Frame (n, frame', (vs', es')) @@ e.at ],
            mem,
            pc,
            bp )
      | Frame (n, frame', (vs', { it = Trapping msg; at } :: es')), vs ->
          (vs, [ Trapping msg @@ at ], mem, pc, bp)
      | Frame (n, frame', (vs', { it = Returning vs0; at } :: es')), vs ->
          (take n vs0 e.at @ vs, [], mem, pc, bp)
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
                call_stack = c.call_stack;
              }
          in
          List.iter
            (fun bp ->
              match bp with
              | Branchpoint _ -> ()
              | Checkpoint cp ->
                  let es' =
                    (Frame (n, !cp.frame, !cp.code) @@ e.at) :: List.tl es
                  and frame' = clone_frame frame in
                  cp := { !cp with frame = frame'; code = (vs, es') })
            c'.bp;
          (vs, [ Frame (n, c'.frame, c'.code) @@ e.at ], c'.mem, c'.pc, c'.bp)
      | Invoke func, vs when c.budget = 0 ->
          (vs, [ Interrupt Limit @@ e.at ], mem, pc, bp)
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
              Stack.push f.at call_stack;
              let locals' =
                List.map
                  (fun v -> (v, Val (Num v)))
                  (List.map
                     (fun t -> Num.default_value (Evaluations.to_num_type t))
                     f.it.locals)
              in
              let locals'' = List.rev args @ locals' in
              let code' = ([], [ Plain (Block (out, f.it.body)) @@ f.at ]) in
              let frame' = { inst = !inst'; locals = List.map ref locals'' } in
              ( vs',
                [ Frame (List.length out, frame', code') @@ e.at ],
                mem,
                pc,
                bp )
          | Interpreter.Func.HostFunc (t, f) -> failwith "HostFunc error")
    in
    step_cnt := !step_cnt + 1;
    { c with code = (vs', es' @ List.tl es); mem = mem'; pc = pc'; bp = bp' }
end

let get_reason (err_t, at) : string =
  let loc =
    Interpreter.Source.string_of_pos at.left
    ^ if at.right = at.left then "" else "-" ^ string_of_pos at.right
  in
  "{" ^ "\"type\" : \"" ^ err_t ^ "\", " ^ "\"line\" : \"" ^ loc ^ "\"" ^ "}"

let write_report error loop_time : unit =
  let spec, reason =
    match error with None -> (true, "{}") | Some e -> (false, get_reason e)
  in
  let report_str =
    "{" ^ "\"specification\": " ^ string_of_bool spec ^ ", " ^ "\"reason\" : "
    ^ reason ^ ", " ^ "\"loop_time\" : \"" ^ string_of_float loop_time ^ "\", "
    ^ "\"solver_time\" : \""
    ^ string_of_float !Batch.solver_time
    ^ "\", " ^ "\"paths_explored\" : " ^ string_of_int !iterations ^ ", "
    ^ "\"solver_counter\" : "
    ^ string_of_int !Batch.solver_count
    ^ ", " ^ "\"instruction_counter\" : " ^ string_of_int !step_cnt ^ "}"
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

let update c (vs, es) pc vars =
  let binds = Batch.value_binds solver vars in
  Store.update c.store binds;
  Heap.update c.mem c.store;
  let f store (_, expr) = (Store.eval store expr, expr) in
  List.iter (fun l -> l := f c.store !l) c.frame.locals;
  let code =
    (List.map (f c.store) vs, List.map (update_admin_instr (f c.store)) es)
  in
  { c with code; pc }

let reset c glob code mem =
  let binds = Batch.value_binds solver (Store.get_key_types c.store) in
  Store.reset c.store;
  Store.init c.store binds;
  let glob = Globals.copy glob in
  Hashtbl.reset c.heap;
  c.tree := head;
  {
    c with
    frame = frame empty_module_inst [];
    code;
    glob;
    mem = Heap.memcpy mem;
    pc = Formula.create ();
    bp = [];
    budget = Interpreter.Flags.budget;
  }

let s_reset (c : config) : config =
  let binds = Batch.value_binds solver (Store.get_key_types c.store) in
  Store.update c.store binds;
  Heap.update c.mem c.store;
  let f store (_, expr) = (Store.eval store expr, expr) in
  List.iter (fun l -> l := f c.store !l) c.frame.locals;
  c.tree := head;
  let vs, es = c.code in
  let code =
    (List.map (f c.store) vs, List.map (update_admin_instr (f c.store)) es)
  in
  { c with code }

module Guided_search (L : WorkList) (S : Stepper) = struct
  let enqueue (pc_wl, cp_wl) branch_points : unit =
    List.iter
      (fun bp ->
        match bp with
        | Branchpoint (pc, node) -> L.push (pc, node) pc_wl
        | Checkpoint cp -> L.push cp cp_wl)
      branch_points

  let rec eval (c : config) wls : config =
    match c.code with
    | vs, [] -> c
    | vs, { it = Trapping msg; at } :: _ -> Trap.error at msg
    | vs, { it = Interrupt Limit; at } :: _ -> { c with code = (vs, []) }
    | vs, { it = Interrupt i; at } :: _ -> c
    | vs, { it = Restart pc; at } :: _ ->
        iterations := !iterations - 1;
        c
    | vs, es ->
        let c' = S.step c in
        enqueue wls c'.bp;
        eval { c' with bp = [] } wls

  let rec find_sat_pc pcs =
    if L.is_empty pcs then None
    else
      let pc, node = L.pop pcs in
      if not (Batch.check_formulas solver [ pc ]) then find_sat_pc pcs
      else Some (pc, Execution_tree.find node)

  let rec find_sat_cp cps =
    if L.is_empty cps then None
    else
      let cp = L.pop cps in
      if not (Batch.check_formulas solver [ !cp.pc ]) then find_sat_cp cps
      else Some (!cp.pc, Some cp)

  let find_sat_path (pcs, cps) =
    match find_sat_cp cps with None -> find_sat_pc pcs | Some _ as cp -> cp

  let invoke (c : config) (test_suite : string) =
    let glob0 = Globals.copy c.glob
    and code0 = c.code
    and mem0 = Heap.memcpy c.mem in
    let pc_wl = L.create () and cp_wl = L.create () in
    (* Main concolic loop *)
    let rec loop c =
      iterations := !iterations + 1;
      let { code; store; bp; tree; _ } = eval c (pc_wl, cp_wl) in
      enqueue (pc_wl, cp_wl) bp;
      match code with
      | vs, { it = Interrupt i; at } :: _ ->
          write_test_case ~witness:true (Store.to_json store);
          Some (string_of_interruption i, at)
      | vs, { it = Restart pc; _ } :: es when Batch.check_formulas solver [ pc ]
        ->
          let tree', _ = Execution_tree.move_true !(c.tree) in
          c.tree := tree';
          loop (update c (vs, es) pc (Store.get_key_types store))
      | _ -> (
          write_test_case (Store.to_json store);
          match find_sat_path (pc_wl, cp_wl) with
          | None -> None
          | Some (pc', None) -> loop (reset c glob0 code0 mem0)
          | Some (pc', Some cp) ->
              let _, c' = clone !cp in
              loop (update c' c'.code c'.pc (Formula.get_symbols pc')))
    in
    loop c

  let s_invoke (c : config) (test_suite : string) : (string * region) option =
    let _, c0 = clone c in
    let wl = L.create () in
    let rec eval (c : config) : config =
      match c.code with
      | vs, [] -> c
      | vs, { it = Trapping msg; at } :: _ -> Trap.error at msg
      | vs, { it = Restart pc; at } :: es -> c
      | vs, { it = Interrupt i; at } :: es -> c
      | vs, es ->
          let c' = S.step c in
          List.iter
            (fun bp ->
              let pc =
                match bp with
                | Checkpoint cp -> !cp.pc
                | Branchpoint (pc, _) -> pc
              in
              L.push pc wl)
            c'.bp;
          eval { c' with bp = [] }
    in
    let rec find_sat_pc pcs =
      if L.is_empty pcs then false
      else if not (Batch.check_formulas solver [ L.pop pcs ]) then
        find_sat_pc pcs
      else true
    in
    (* Main concolic loop *)
    let rec loop (c : config) =
      iterations := !iterations + 1;
      let { code; store; bp; pc; _ } = eval c in
      List.iter
        (fun bp ->
          let pc =
            match bp with Checkpoint cp -> !cp.pc | Branchpoint (pc, _) -> pc
          in
          L.push pc wl)
        bp;
      match code with
      | vs, { it = Interrupt i; at } :: _ ->
          write_test_case ~witness:true (Store.to_json store);
          Some (string_of_interruption i, at)
      | vs, { it = Restart pc; _ } :: es ->
          print_endline "--- attempting restart ---";
          iterations := !iterations - 1;
          if Batch.check_formulas solver [ pc ] then
            loop (update c (vs, es) pc (Store.get_key_types store))
          else if L.is_empty wl || not (find_sat_pc wl) then None
          else
            let _, c' = clone c0 in
            loop (s_reset c')
      | _ ->
          write_test_case (Store.to_json store);
          if L.is_empty wl || not (find_sat_pc wl) then None
          else
            let _, c' = clone c0 in
            loop (s_reset c')
    in
    let error = loop c in
    error

  let p_invoke (c : config) (test_suite : string) :
      (Formula.t, string * region) result =
    let rec eval (c : config) : config =
      match c.code with
      | vs, [] -> c
      | vs, { it = Trapping msg; at } :: _ -> Trap.error at msg
      | vs, { it = Restart pc; at } :: es ->
          c (* TODO: probably need to change this *)
      | vs, { it = Interrupt i; at } :: es -> c
      | vs, es ->
          let c' = S.step c in
          eval c'
    in
    let c' = eval c in
    let res =
      match c'.code with
      | vs, { it = Interrupt i; at } :: _ ->
          write_test_case ~witness:true (Store.to_json c'.store);
          Result.error (string_of_interruption i, at)
      | _ ->
          write_test_case (Store.to_json c'.store);
          Result.ok c.pc
    in
    res
end

module NoCheckpointStepper = ConcolicStepper (NoCheckpoint)
module FuncCheckpointStepper = ConcolicStepper (FuncCheckpoint)
module RandCheckpointStepper = ConcolicStepper (RandCheckpoint)
module DepthCheckpointStepper = ConcolicStepper (DepthCheckpoint)
module DFS = Guided_search (Stack) (NoCheckpointStepper)
module BFS = Guided_search (Queue) (NoCheckpointStepper)
module RND = Guided_search (RandArray) (NoCheckpointStepper)

let set_timeout (time_limit : int) : unit =
  let alarm_handler i : unit =
    Batch.interrupt ();
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
  let glob =
    Globals.of_seq
      (Seq.mapi
         (fun i a ->
           let v = Global.load a in
           ( Int32.of_int i,
             (Evaluations.of_value v, Val (Num (Evaluations.of_value v))) ))
         (List.to_seq inst.globals))
  in
  let c =
    config empty_module_inst (List.rev vs)
      [ Invoke func @@ at ]
      mem0 glob (ref head)
  in
  let invoke =
    match parse_policy !Flags.policy with
    | None -> Crash.error at ("invalid search policy '" ^ !Flags.policy ^ "'")
    | Some Depth -> DFS.invoke
    | Some Breadth -> BFS.invoke
    | Some Random -> RND.invoke
  in
  loop_start := Sys.time ();
  let error = invoke c test_suite in
  write_report error (Sys.time () -. !loop_start)

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
