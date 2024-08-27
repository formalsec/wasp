open Smtml
open Value
module Ast = Interpreter.Ast
module Batch = Smtml.Solver.Batch (Smtml.Z3_mappings)
module Bug = Common.Bug
module Counter = Common.Counter
module Crash = Common.Crash
module Chunktable = Common.Chunktable

module Evaluations = struct
  include Common.Evaluations
  include Evaluations
end

module Flags = Interpreter.Flags
module Globals = Common.Globals
module Instance = Interpreter.Instance
module Source = Interpreter.Source
module Trap = Common.Trap
module Types = Interpreter.Types

let memory_error at = function
  | Heap.InvalidAddress a ->
    Int64.to_string a ^ ":address not found in hashtable"
  | Heap.Bounds -> "out of bounds memory access"
  | Interpreter.Memory.SizeOverflow -> "memory size overflow"
  | Interpreter.Memory.SizeLimit -> "memory size limit reached"
  | Interpreter.Memory.Type -> Crash.error at "type mismatch at memory access"
  | exn -> raise exn

type policy =
  | Random
  | Depth
  | Breadth

type interruption =
  | Limit
  | Failure of Expr.t
  | Bug of Bug.bug

type value = Num.t * Expr.t

type 'a stack = 'a list

type frame =
  { inst : Instance.module_inst
  ; locals : value ref list
  }

type code = value stack * sym_admin_instr list

and sym_admin_instr = sym_admin_instr' Source.phrase

and sym_admin_instr' =
  | Plain of Ast.instr'
  | Invoke of Instance.func_inst
  | Trapping of string
  | Returning of value stack
  | Breaking of int32 * value stack
  | Label of int * Ast.instr list * code
  | Frame of int * frame * code
  | Interrupt of interruption
  | Restart of Expr.t

type config =
  { frame : frame
  ; glob : value Globals.t
  ; code : code
  ; mem : Heap.t
  ; store : Store.t
  ; heap : Chunktable.t
  ; pc : Expr.t
  ; bp : bp list
  ; tree : tree ref
  ; budget : int
  ; call_stack : Source.region Stack.t
  }

and tree = config ref Execution_tree.t ref

and bp =
  | Branchpoint of Expr.t * tree
  | Checkpoint of config ref

let frame inst locals = { inst; locals }

let clone_frame (f : frame) : frame =
  frame f.inst (List.map (fun l -> ref !l) f.locals)

let rec clone_admin_instr e =
  let open Source in
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
  let frame = clone_frame c.frame in
  let glob = Globals.copy c.glob in
  let code = (vs, List.map clone_admin_instr es) in
  let mem, mem' = Heap.clone c.mem in
  let store = Store.copy c.store in
  let heap = Chunktable.copy c.heap in
  let pc = c.pc in
  let bp = [] in
  let tree = ref !(c.tree) in
  let budget = c.budget in
  let call_stack = Stack.copy c.call_stack in
  ( mem'
  , { frame; glob; code; mem; store; heap; pc; bp; tree; budget; call_stack } )

let config inst vs es mem glob tree =
  { frame = frame inst []
  ; glob
  ; code = (vs, es)
  ; mem
  ; store = Store.create []
  ; heap = Chunktable.create ()
  ; pc = Expr.value True
  ; bp = []
  ; tree
  ; budget = Interpreter.Flags.budget
  ; call_stack = Stack.create ()
  }

exception BugException of config * Source.region * Bug.bug

let head = ref Execution_tree.(Node (None, None, ref Leaf, ref Leaf))

let step_cnt = ref 0

let iterations = ref 0

let loop_start = ref 0.

let logs = ref []

let solver = Batch.create ()

let debug0 fmt =
  if !Flags.trace then
    let t = Format.dprintf fmt in
    Format.eprintf "WASP: %t" t

let debug1 fmt a =
  if !Flags.trace then
    let t = Format.dprintf fmt a in
    Format.eprintf "WASP: %t" t

let debug2 fmt a b =
  if !Flags.trace then
    let t = Format.dprintf fmt a b in
    Format.eprintf "WASP: %t" t

let debug3 fmt a b c =
  if !Flags.trace then
    let t = Format.dprintf fmt a b c in
    Format.eprintf "WASP: %t" t

let pp_interruption fmt = function
  | Limit -> Fmt.string fmt "Reached Analysis Limit"
  | Failure _ -> Fmt.string fmt "Reached Assertion Failure"
  | Bug b -> Fmt.pf fmt "Found: %a" Bug.pp b

let plain e =
  let open Source in
  Plain e.it @@ e.at

let lookup category list x =
  let open Source in
  try Interpreter.Lib.List32.nth list x.it
  with Failure _ ->
    Crash.error x.at ("undefined " ^ category ^ " " ^ Int32.to_string x.it)

let type_ (inst : Instance.module_inst) x = lookup "type" inst.types x

let func (inst : Instance.module_inst) x = lookup "function" inst.funcs x

let table (inst : Instance.module_inst) x = lookup "table" inst.tables x

let memory (inst : Instance.module_inst) x = lookup "memory" inst.memories x

let global (inst : Instance.module_inst) x = lookup "global" inst.globals x

let local (frame : frame) x = lookup "local" frame.locals x

let elem inst x i at =
  match Interpreter.Table.load (table inst x) i with
  | Interpreter.Table.Uninitialized ->
    Trap.error at ("uninitialized element " ^ Int32.to_string i)
  | f -> f
  | exception Interpreter.Table.Bounds ->
    Trap.error at ("undefined element " ^ Int32.to_string i)

let func_elem inst x i at =
  let open Instance in
  match elem inst x i at with
  | FuncElem f -> f
  | _ -> Crash.error at ("type mismatch for element " ^ Int32.to_string i)

let take n (vs : 'a stack) at =
  try Interpreter.Lib.List.take n vs
  with Failure _ -> Crash.error at "stack underflow"

let drop n (vs : 'a stack) at =
  try Interpreter.Lib.List.drop n vs
  with Failure _ -> Crash.error at "stack underflow"

let default_value = function
  | Ty.Ty_bitv 32 -> Num.I32 0l
  | Ty.Ty_bitv 64 -> I64 0L
  | Ty.Ty_fp 32 -> F32 (Int32.bits_of_float 0.)
  | Ty.Ty_fp 64 -> F64 (Int64.bits_of_float 0.)
  | _ -> assert false

let int32 e =
  match Expr.view e with
  | Val True -> Expr.value (Num (I32 1l))
  | Val False -> Expr.value (Num (I32 0l))
  | Cvtop (Ty_bitv 32, ToBool, e) -> e
  | _ -> Expr.cvtop (Ty_bitv 32) OfBool e

let to_relop e =
  match Expr.view e with
  | Val _ | Ptr _ -> None
  | Relop _ -> Some e
  | Cvtop (_, OfBool, cond) -> Some cond
  | _ -> Some (Expr.relop Ty_bool Ne e (Expr.value (Num (I32 0l))))

let mk_relop ?(reduce : bool = true) (e : Expr.t) (ty : Ty.t) =
  let e = if reduce then Expr.simplify e else e in
  match Expr.view e with
  | Relop _ -> e
  | _ -> (
    let zero = Value.Num (default_value ty) in
    Expr.simplify
    @@
    match ty with
    | Ty_bitv 32 -> Expr.relop Ty_bool Ne e (Expr.value zero)
    | Ty_bitv 64 -> Expr.relop Ty_bool Ne e (Expr.value zero)
    | Ty_fp 32 -> Expr.relop (Ty_fp 32) Ne e (Expr.value zero)
    | Ty_fp 64 -> Expr.relop (Ty_fp 64) Ne e (Expr.value zero)
    | _ -> assert false )

let add_constraint ?(neg : bool = false) e pc =
  let cond =
    let e = Expr.simplify e in
    let c = to_relop e in
    if neg then Option.map (fun e -> Expr.Bool.not e) c else c
  in
  match (cond, Expr.view pc) with
  | None, _ -> pc
  | Some cond, Val True -> cond
  | Some cond, _ -> Expr.binop Ty_bool And cond pc

let branch_on_cond bval c pc tree =
  let tree', to_branch =
    if bval then Execution_tree.move_true !tree
    else Execution_tree.move_false !tree
  in
  tree := tree';
  if to_branch then (
    debug2 "Branching on: %a@." Expr.pp c;
    Some (add_constraint ~neg:bval c pc) )
  else None

let concretize_base_ptr e =
  match Expr.view e with Ptr { base; _ } -> Some base | _ -> None

module NoCheckpoint : Checkpoint_intf.S with type config = config = struct
  type nonrec config = config

  let is_checkpoint (_ : config) : bool = false
end

module FuncCheckpoint : Checkpoint_intf.S with type config = config = struct
  type nonrec config = config

  let visited = Hashtbl.create Interpreter.Flags.hashtbl_default_size

  let is_checkpoint (c : config) : bool =
    let func = Stack.top c.call_stack in
    if Hashtbl.mem visited func then false
    else (
      Hashtbl.add visited func true;
      Execution_tree.can_branch !(c.tree) )
end

module RandCheckpoint : Checkpoint_intf.S with type config = config = struct
  type nonrec config = config

  let is_checkpoint (c : config) : bool =
    Execution_tree.can_branch !(c.tree) && Random.bool ()
end

module DepthCheckpoint : Checkpoint_intf.S with type config = config = struct
  type nonrec config = config

  let _ = Counter.create ()

  let is_checkpoint (_c : config) : bool = false
  (* let size_pc = Expression.length c.pc in *)
  (* Execution_tree.can_branch !(c.tree) *)
  (* && size_pc mod 10 = 0 *)
  (* && Counter.get_and_inc count size_pc < 5 *)
end

module type Stepper = sig
  val step : config -> config
end

module ConcolicStepper (C : Checkpoint_intf.S with type config = config) :
  Stepper = struct
  open Source

  let pp_value fmt (n, e) = Format.fprintf fmt "(%a, %a)" Num.pp n Expr.pp e

  let pp_value_list fmt vs =
    Format.pp_print_list
      ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
      pp_value fmt vs

  let rec step (c : config) : config =
    let { frame
        ; glob
        ; code = vs, es
        ; mem
        ; store
        ; heap
        ; pc
        ; bp
        ; tree
        ; call_stack
        ; _
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
        | Loop (_, es'), vs ->
          ( vs
          , [ Label (0, [ e' @@ e.at ], ([], List.map plain es')) @@ e.at ]
          , mem
          , pc
          , bp )
        | If (ts, es1, es2), (I32 i, ex) :: vs'
          when not Expr.(is_symbolic (simplify ex)) ->
          if i = 0l then (vs', [ Plain (Block (ts, es2)) @@ e.at ], mem, pc, bp)
          else (vs', [ Plain (Block (ts, es1)) @@ e.at ], mem, pc, bp)
        | If (ts, es1, es2), (I32 i, ex) :: vs' ->
          let b, es1', es2' =
            ( i <> 0l
            , [ Plain (Block (ts, es1)) @@ e.at ]
            , [ Plain (Block (ts, es2)) @@ e.at ] )
          in
          let mem', bp =
            let pc' = add_constraint ~neg:b ex pc in
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
            match branch_on_cond b ex pc tree with
            | None -> bp
            | Some pc -> Branchpoint (pc, !tree) :: bp
          in
          let pc' = add_constraint ~neg:(not b) ex pc in
          (vs', (if b then es1' else es2'), mem', pc', bp')
        | Br x, vs -> ([], [ Breaking (x.it, vs) @@ e.at ], mem, pc, bp)
        | BrIf x, (I32 i, ex) :: vs' when not Expr.(is_symbolic (simplify ex))
          ->
          if i = 0l then (vs', [], mem, pc, bp)
          else (vs', [ Plain (Br x) @@ e.at ], mem, pc, bp)
        | BrIf x, (I32 i, ex) :: vs' ->
          let b, es1', es2' = (i <> 0l, [ Plain (Br x) @@ e.at ], []) in
          let mem', bp =
            let pc' = add_constraint ~neg:b ex pc in
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
            match branch_on_cond b ex pc tree with
            | None -> bp
            | Some pc -> Branchpoint (pc, !tree) :: bp
          in
          let pc' = add_constraint ~neg:(not b) ex pc in
          (vs', (if b then es1' else es2'), mem', pc', bp')
        | BrTable (xs, x), (I32 i, _) :: vs'
          when Interpreter.I32.ge_u i (Interpreter.Lib.List32.length xs) ->
          (vs', [ Plain (Br x) @@ e.at ], mem, pc, bp)
        | BrTable (xs, _), (I32 i, _) :: vs' ->
          ( vs'
          , [ Plain (Br (Interpreter.Lib.List32.nth xs i)) @@ e.at ]
          , mem
          , pc
          , bp )
        | Return, vs -> ([], [ Returning vs @@ e.at ], mem, pc, bp)
        | Call x, vs -> (vs, [ Invoke (func frame.inst x) @@ e.at ], mem, pc, bp)
        | CallIndirect x, (I32 i, _) :: vs ->
          let func = func_elem frame.inst (0l @@ e.at) i e.at in
          if type_ frame.inst x <> Interpreter.Func.type_of func then
            (vs, [ Trapping "indirect call type mismatch" @@ e.at ], mem, pc, bp)
          else (vs, [ Invoke func @@ e.at ], mem, pc, bp)
        | Drop, _ :: vs' -> (vs', [], mem, pc, bp)
        | Select, (I32 i, ve) :: v2 :: v1 :: vs'
          when not Expr.(is_symbolic (simplify ve)) ->
          if i = 0l then (v2 :: vs', [], mem, pc, bp)
          else (v1 :: vs', [], mem, pc, bp)
        | Select, (I32 i, ve) :: v2 :: v1 :: vs' ->
          let b, vs1, vs2 = (i <> 0l, v1 :: vs', v2 :: vs') in
          let mem', bp =
            let pc' = add_constraint ~neg:b ve pc in
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
            match branch_on_cond b ve pc tree with
            | None -> bp
            | Some pc -> Branchpoint (pc, !tree) :: bp
          in
          let pc' = add_constraint ~neg:(not b) ve pc in
          ((if b then vs1 else vs2), [], mem', pc', bp')
        | LocalGet x, vs -> (!(local frame x) :: vs, [], mem, pc, bp)
        | LocalSet x, (v, ex) :: vs' ->
          local frame x := (v, Expr.simplify ex);
          (vs', [], mem, pc, bp)
        | LocalTee x, (v, ex) :: vs' ->
          local frame x := (v, Expr.simplify ex);
          (!(local frame x) :: vs', [], mem, pc, bp)
        | GlobalGet x, vs -> (Globals.find glob x.it :: vs, [], mem, pc, bp)
        | GlobalSet x, v :: vs' ->
          Globals.add glob x.it v;
          (vs', [], mem, pc, bp)
        | Load { offset; ty; sz; _ }, (I32 i, sym_ptr) :: vs' -> (
          try
            let base = Interpreter.I64_convert.extend_i32_u i in
            (* overflow check *)
            let ptr = concretize_base_ptr (Expr.simplify sym_ptr) in
            match
              Option.bind ptr (fun bp ->
                  Chunktable.check_access heap bp (I32 i) offset )
            with
            | Some b -> (vs', [ Interrupt (Bug b) @@ e.at ], mem, pc, bp)
            | None ->
              let ty = Common.Evaluations.ty_of_num_type ty in
              let v, e =
                match sz with
                | None -> Heap.load_value mem base offset ty
                | Some (sz, ext) -> Heap.load_packed sz ext mem base offset ty
              in
              ((v, e) :: vs', [], mem, pc, bp)
          with exn ->
            (vs', [ Trapping (memory_error e.at exn) @@ e.at ], mem, pc, bp) )
        | Store { offset; sz; _ }, (v, ex) :: (I32 i, sym_ptr) :: vs' -> (
          try
            let base = Interpreter.I64_convert.extend_i32_u i in
            let ptr = concretize_base_ptr (Expr.simplify sym_ptr) in
            match
              Option.bind ptr (fun bp ->
                  Chunktable.check_access heap bp (I32 i) offset )
            with
            | Some b -> (vs', [ Interrupt (Bug b) @@ e.at ], mem, pc, bp)
            | None ->
              let ex = Expr.simplify ex in
              ( match sz with
              | None -> Heap.store_value mem base offset (v, ex)
              | Some sz -> Heap.store_packed sz mem base offset (v, ex) );
              (vs', [], mem, pc, bp)
          with exn ->
            (vs', [ Trapping (memory_error e.at exn) @@ e.at ], mem, pc, bp) )
        | MemorySize, vs ->
          let mem' = memory frame.inst (0l @@ e.at) in
          let v : Num.t = I32 (Interpreter.Memory.size mem') in
          ((v, Expr.value (Num v)) :: vs, [], mem, pc, bp)
        | MemoryGrow, (I32 delta, _) :: vs' ->
          let mem' = memory frame.inst (0l @@ e.at) in
          let old_size = Interpreter.Memory.size mem' in
          let result =
            let open Interpreter in
            Num.I32
              ( try
                  Memory.grow mem' delta;
                  old_size
                with
                | Memory.SizeOverflow | Memory.SizeLimit | Memory.OutOfMemory ->
                  -1l )
          in
          ((result, Expr.value (Num result)) :: vs', [], mem, pc, bp)
        | Const v, vs ->
          let v = Evaluations.of_value v.it in
          ((v, Expr.value (Num v)) :: vs, [], mem, pc, bp)
        | Test testop, v :: vs' -> (
          try (Evaluations.eval_testop v testop :: vs', [], mem, pc, bp)
          with exn ->
            ( vs'
            , [ Trapping (Common.numeric_error e.at exn) @@ e.at ]
            , mem
            , pc
            , bp ) )
        | Compare relop, v2 :: v1 :: vs' -> (
          let v, expr = Evaluations.eval_relop v1 v2 relop in
          try ((v, int32 expr) :: vs', [], mem, pc, bp)
          with exn ->
            ( vs'
            , [ Trapping (Common.numeric_error e.at exn) @@ e.at ]
            , mem
            , pc
            , bp ) )
        | Unary unop, v :: vs' -> (
          try (Evaluations.eval_unop v unop :: vs', [], mem, pc, bp)
          with exn ->
            ( vs'
            , [ Trapping (Common.numeric_error e.at exn) @@ e.at ]
            , mem
            , pc
            , bp ) )
        | Binary binop, v2 :: v1 :: vs' -> (
          try (Evaluations.eval_binop v1 v2 binop :: vs', [], mem, pc, bp)
          with exn ->
            ( vs'
            , [ Trapping (Common.numeric_error e.at exn) @@ e.at ]
            , mem
            , pc
            , bp ) )
        | Convert cvtop, v :: vs' -> (
          try (Evaluations.eval_cvtop cvtop v :: vs', [], mem, pc, bp)
          with exn ->
            ( vs'
            , [ Trapping (Common.numeric_error e.at exn) @@ e.at ]
            , mem
            , pc
            , bp ) )
        | Dup, v :: vs' -> (v :: v :: vs', [], mem, pc, bp)
        | SymAssert, (I32 0l, ex) :: vs' ->
          debug2 "Assertion failure: %a@." Expr.pp ex;
          (vs', [ Interrupt (Failure pc) @@ e.at ], mem, pc, bp)
        | SymAssert, (I32 _, ex) :: vs' when not Expr.(is_symbolic (simplify ex))
          ->
          (vs', [], mem, pc, bp)
        | SymAssert, (I32 _, ex) :: vs' -> (
          let formulas = add_constraint ~neg:true ex pc in
          debug2 "Testing assertion: %a@." Expr.pp formulas;
          match Batch.check solver [ formulas ] with
          | `Unsat -> (vs', [], mem, pc, bp)
          | `Sat -> (
            match Batch.model solver ~symbols:(Store.get_key_types store) with
            | None -> assert false
            | Some model ->
              let binds = Model.get_bindings model in
              Store.update store binds;
              (vs', [ Interrupt (Failure pc) @@ e.at ], mem, pc, bp) )
          | `Unknown -> assert false )
        | SymAssume, (I32 i, ex) :: vs' when not Expr.(is_symbolic (simplify ex))
          ->
          let unsat = Expr.value False in
          if i = 0l then (vs', [ Restart unsat @@ e.at ], mem, pc, bp)
          else (vs', [], mem, pc, bp)
        | SymAssume, (I32 i, ex) :: vs' ->
          if i = 0l then (
            debug2 "Assumption failure: %a@." Expr.pp ex;
            (vs', [ Restart (add_constraint ex pc) @@ e.at ], mem, pc, bp) )
          else (
            debug0 "Assumption holds@.";
            let tree', _ = Execution_tree.move_true !tree in
            tree := tree';
            (vs', [], mem, add_constraint ex pc, bp) )
        | Symbolic (ty, b), (I32 i, _) :: vs' ->
          let base = Interpreter.I64_convert.extend_i32_u i in
          let symbol = if i = 0l then "x" else Heap.load_string mem base in
          let x = Store.next store symbol in
          let ty' = Evaluations.ty_of_num_type ty in
          let v = Store.get store x ty' b in
          ((v, Expr.symbol (Symbol.make ty' x)) :: vs', [], mem, pc, bp)
        | Boolop boolop, (v2, sv2) :: (v1, sv1) :: vs' -> (
          let sv2' = mk_relop sv2 (Num.type_of v2) in
          let v2' =
            Num.(num_of_bool (not (v2 = default_value (Num.type_of v2))))
          in
          let sv1' = mk_relop sv1 (Num.type_of v1) in
          let v1' = Num.(num_of_bool (not (v1 = default_value (type_of v1)))) in
          try
            let v3, sv3 =
              Evaluations.eval_binop (v1', sv1') (v2', sv2') boolop
            in
            ((v3, Expr.simplify sv3) :: vs', [], mem, pc, bp)
          with exn ->
            ( vs'
            , [ Trapping (Common.numeric_error e.at exn) @@ e.at ]
            , mem
            , pc
            , bp ) )
        | Alloc, (I32 size, _) :: (I32 base, _) :: vs' ->
          let ptr = Expr.ptr base (Expr.value (Num (I32 0l))) in
          Hashtbl.add heap base size;
          ((I32 base, ptr) :: vs', [], mem, pc, bp)
        | Free, (I32 i, _) :: vs' ->
          let es' =
            if not (Hashtbl.mem heap i) then
              [ Interrupt (Bug Bug.InvalidFree) @@ e.at ]
            else (
              Hashtbl.remove heap i;
              [] )
          in
          (vs', es', mem, pc, bp)
        | GetSymInt32 x, vs' ->
          let v =
            try Store.find store x
            with Not_found ->
              Crash.error e.at "Symbolic variable was not in store."
          in
          ((v, Expr.symbol (Symbol.make (Ty_bitv 32) x)) :: vs', [], mem, pc, bp)
        | GetSymInt64 x, vs' ->
          let v =
            try Store.find store x
            with Not_found ->
              Crash.error e.at "Symbolic variable was not in store."
          in
          ((v, Expr.symbol (Symbol.make (Ty_bitv 64) x)) :: vs', [], mem, pc, bp)
        | GetSymFloat32 x, vs' ->
          let v =
            try Store.find store x
            with Not_found ->
              Crash.error e.at "Symbolic variable was not in store."
          in
          ((v, Expr.symbol (Symbol.make (Ty_fp 32) x)) :: vs', [], mem, pc, bp)
        | GetSymFloat64 x, vs' ->
          let v =
            try Store.find store x
            with Not_found ->
              Crash.error e.at "Symbolic variable was not in store."
          in
          ((v, Expr.symbol (Symbol.make (Ty_fp 64) x)) :: vs', [], mem, pc, bp)
        | TernaryOp, (I32 r2, s_r2) :: (I32 r1, s_r1) :: (I32 c, s_c) :: vs' ->
          let r : Num.t = I32 (if c = 0l then r2 else r1) in
          let s_c' = to_relop (Expr.simplify s_c) in
          let v, pc' =
            match s_c' with
            | None -> ((r, if c = 0l then s_r2 else s_r1), pc)
            | Some s ->
              let x = Store.next store "__ternary" in
              Store.add store x r;
              let s_x = Expr.symbol (Symbol.make (Ty_bitv 32) x) in
              let t_eq = Expr.relop Ty_bool Eq s_x s_r1 in
              let t_imp =
                Expr.binop (Ty_bitv 32) Or (Expr.unop Ty_bool Not s) t_eq
              in
              let f_eq = Expr.relop Ty_bool Eq s_x s_r2 in
              let f_imp = Expr.binop (Ty_bitv 32) Or s f_eq in
              let cond = Expr.binop (Ty_bitv 32) And t_imp f_imp in
              ( (r, s_x)
              , add_constraint
                  (Expr.relop Ty_bool Ne cond (Expr.value (Num (I32 0l))))
                  pc )
          in
          (v :: vs', [], mem, pc', bp)
        | PrintStack, vs' ->
          debug3 "Stack @@ %s:@\n  @[<v>%a@]@."
            (Interpreter.Source.string_of_pos e.at.left)
            pp_value_list vs';
          (vs', [], mem, pc, bp)
        | PrintPC, vs' ->
          debug3 "%s:PC: %a@."
            (Interpreter.Source.string_of_pos e.at.left)
            Expr.pp pc;
          (vs', [], mem, pc, bp)
        | PrintMemory, vs' ->
          debug1 "Mem:@\n%s@." (Heap.to_string mem);
          (vs', [], mem, pc, bp)
        | PrintBtree, vs' ->
          (* Btree.print_b_tree mem; *)
          (vs', [], mem, pc, bp)
        | CompareExpr, (v1, ex1) :: (v2, ex2) :: vs' ->
          let res : Num.t * Expr.t =
            match (Expr.view ex1, Expr.view ex2) with
            | Symbol s1, Symbol s2 ->
              if Symbol.equal s1 s2 then (I32 1l, Expr.relop Ty_bool Eq ex1 ex2)
              else (I32 0l, Expr.relop Ty_bool Ne ex1 ex2)
            | _, _ ->
              Evaluations.eval_relop (v1, ex1) (v2, ex2)
                (Interpreter.Values.I32 Interpreter.Ast.I32Op.Eq)
          in
          (res :: vs', [], mem, pc, bp)
        | IsSymbolic, (I32 n, _) :: (I32 i, _) :: vs' ->
          let base = Interpreter.I64_convert.extend_i32_u i in
          let _, v = Heap.load_bytes mem base (Int32.to_int n) in
          let result = Num.num_of_bool (Expr.is_symbolic v) in
          ((result, Expr.value (Num result)) :: vs', [], mem, pc, bp)
        | SetPriority, _ :: _ :: _ :: vs' -> (vs', [], mem, pc, bp)
        | PopPriority, _ :: vs' -> (vs', [], mem, pc, bp)
        | _ -> Crash.error e.at "missing or ill-typed operand on stack" )
      | Trapping _, _ -> assert false
      | Interrupt _, _ -> assert false
      | Restart _, _ -> assert false
      | Returning _, _ -> Crash.error e.at "undefined frame"
      | Breaking (_, _), _ -> Crash.error e.at "undefined label"
      | Label (_, _, (vs', [])), vs -> (vs' @ vs, [], mem, pc, bp)
      | Label (n, es0, (vs', { it = Restart pc'; at } :: es')), vs ->
        ( vs
        , [ Restart pc' @@ at; Label (n, es0, (vs', es')) @@ e.at ]
        , mem
        , pc
        , bp )
      | Label (n, es0, (vs', { it = Interrupt i; at } :: es')), vs ->
        ( vs
        , [ Interrupt i @@ at; Label (n, es0, (vs', es')) @@ e.at ]
        , mem
        , pc
        , bp )
      | Label (_, _, (_, { it = Trapping msg; at } :: _)), vs ->
        (vs, [ Trapping msg @@ at ], mem, pc, bp)
      | Label (_, _, (_, { it = Returning vs0; at } :: _)), vs ->
        (vs, [ Returning vs0 @@ at ], mem, pc, bp)
      | Label (n, es0, (_, { it = Breaking (0l, vs0); _ } :: _)), vs ->
        (take n vs0 e.at @ vs, List.map plain es0, mem, pc, bp)
      | Label (_, _, (_, { it = Breaking (k, vs0); at } :: _)), vs ->
        (vs, [ Breaking (Int32.sub k 1l, vs0) @@ at ], mem, pc, bp)
      | Label (n, es0, code'), vs ->
        let c' = step { c with code = code' } in
        List.iter
          (fun bp ->
            match bp with
            | Branchpoint _ -> ()
            | Checkpoint cp ->
              let es' = (Label (n, es0, !cp.code) @@ e.at) :: List.tl es in
              cp := { !cp with code = (vs, es') } )
          c'.bp;
        (vs, [ Label (n, es0, c'.code) @@ e.at ], c'.mem, c'.pc, c'.bp)
      | Frame (_, _, (vs', [])), vs ->
        ignore (Stack.pop call_stack);
        (vs' @ vs, [], mem, pc, bp)
      | Frame (n, frame', (vs', { it = Restart pc'; at } :: es')), vs ->
        ( vs
        , [ Restart pc' @@ at; Frame (n, frame', (vs', es')) @@ e.at ]
        , mem
        , pc
        , bp )
      | Frame (n, frame', (vs', { it = Interrupt i; at } :: es')), vs ->
        ( vs
        , [ Interrupt i @@ at; Frame (n, frame', (vs', es')) @@ e.at ]
        , mem
        , pc
        , bp )
      | Frame (_, _, (_, { it = Trapping msg; at } :: _)), vs ->
        (vs, [ Trapping msg @@ at ], mem, pc, bp)
      | Frame (n, _, (_, { it = Returning vs0; _ } :: _)), vs ->
        (take n vs0 e.at @ vs, [], mem, pc, bp)
      | Frame (n, frame', code'), vs ->
        let c' =
          step
            { frame = frame'
            ; glob = c.glob
            ; code = code'
            ; mem = c.mem
            ; heap = c.heap
            ; store = c.store
            ; pc = c.pc
            ; bp = c.bp
            ; tree = c.tree
            ; budget = c.budget - 1
            ; call_stack = c.call_stack
            }
        in
        List.iter
          (fun bp ->
            match bp with
            | Branchpoint _ -> ()
            | Checkpoint cp ->
              let es' = (Frame (n, !cp.frame, !cp.code) @@ e.at) :: List.tl es
              and frame' = clone_frame frame in
              cp := { !cp with frame = frame'; code = (vs, es') } )
          c'.bp;
        (vs, [ Frame (n, c'.frame, c'.code) @@ e.at ], c'.mem, c'.pc, c'.bp)
      | Invoke _, vs when c.budget = 0 ->
        (vs, [ Interrupt Limit @@ e.at ], mem, pc, bp)
      | Invoke func, vs -> (
        let symbolic_arg ty =
          let x = Store.next store "arg" in
          let v = Store.get store x ty false in
          (v, Expr.symbol (Symbol.make ty x))
        in
        let (Interpreter.Types.FuncType (ins, out)) =
          Interpreter.Func.type_of func
        in
        let n = List.length ins in
        let vs =
          if n > 0 && List.length vs = 0 then
            List.map (fun t -> symbolic_arg (Evaluations.ty_of_num_type t)) ins
          else vs
        in
        let args, vs' = (take n vs e.at, drop n vs e.at) in
        match func with
        | Interpreter.Func.AstFunc (_, inst', f) ->
          Stack.push f.at call_stack;
          let locals' =
            List.map
              (fun v -> (v, Expr.value (Num v)))
              (List.map
                 (fun t -> default_value (Evaluations.ty_of_num_type t))
                 f.it.locals )
          in
          let locals'' = List.rev args @ locals' in
          let code' = ([], [ Plain (Block (out, f.it.body)) @@ f.at ]) in
          let frame' = { inst = !inst'; locals = List.map ref locals'' } in
          (vs', [ Frame (List.length out, frame', code') @@ e.at ], mem, pc, bp)
        | HostFunc (FuncType ([], [ Types.I32Type ]), _) ->
          let x = Store.next store "symbol" in
          let ty = Ty.Ty_bitv 32 in
          let v = Store.get store x ty false in
          ((v, Expr.symbol (Symbol.make ty x)) :: vs', [], mem, pc, bp)
        | HostFunc (_, _) -> failwith "Unknown host func" )
    in
    step_cnt := !step_cnt + 1;
    { c with code = (vs', es' @ List.tl es); mem = mem'; pc = pc'; bp = bp' }
end

let get_reason (err_t, at) : string =
  let open Source in
  let loc =
    Source.string_of_pos at.left
    ^ if at.right = at.left then "" else "-" ^ string_of_pos at.right
  in
  "{" ^ "\"type\" : \"" ^ err_t ^ "\", " ^ "\"line\" : \"" ^ loc ^ "\"" ^ "}"

let write_report error loop_time : unit =
  if !Interpreter.Flags.log then Common.print_logs !logs;
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
  let open Source in
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

let update c (vs, es) pc symbols =
  let model = Option.get (Batch.model ~symbols solver) in
  let binds = Model.get_bindings model in
  Store.update c.store binds;
  Heap.update c.mem c.store;
  let f store (_, expr) =
    ((match Store.eval store expr with Num n -> n | _ -> assert false), expr)
  in
  List.iter (fun l -> l := f c.store !l) c.frame.locals;
  let code =
    (List.map (f c.store) vs, List.map (update_admin_instr (f c.store)) es)
  in
  { c with code; pc }

let reset c glob code mem =
  let model =
    Option.get (Batch.model ~symbols:(Store.get_key_types c.store) solver)
  in
  let binds = Model.get_bindings model in
  Store.reset c.store;
  Store.init c.store binds;
  let glob = Globals.copy glob in
  Hashtbl.reset c.heap;
  c.tree := head;
  { c with
    frame = frame Instance.empty_module_inst []
  ; code
  ; glob
  ; mem = Heap.memcpy mem
  ; pc = Expr.value True
  ; bp = []
  ; budget = Interpreter.Flags.budget
  }

let s_reset (c : config) : config =
  let model =
    Option.get (Batch.model ~symbols:(Store.get_key_types c.store) solver)
  in
  let binds = Model.get_bindings model in
  Store.update c.store binds;
  Heap.update c.mem c.store;
  let f store (_, expr) =
    ((match Store.eval store expr with Num n -> n | _ -> assert false), expr)
  in
  List.iter (fun l -> l := f c.store !l) c.frame.locals;
  c.tree := head;
  let vs, es = c.code in
  let code =
    (List.map (f c.store) vs, List.map (update_admin_instr (f c.store)) es)
  in
  { c with code }

module Guided_search (L : Common.WorkList) (S : Stepper) = struct
  let enqueue (pc_wl, cp_wl) branch_points : unit =
    List.iter
      (fun bp ->
        match bp with
        | Branchpoint (pc, node) -> L.push (pc, node) pc_wl
        | Checkpoint cp -> L.push cp cp_wl )
      branch_points

  let rec eval_loop (c : config) wls : config =
    match c.code with
    | _, [] -> c
    | _, { it = Trapping _; _ } :: _ -> c
    | vs, { it = Interrupt Limit; _ } :: _ -> { c with code = (vs, []) }
    | _, { it = Interrupt _; _ } :: _ -> c
    | _, { it = Restart _; _ } :: _ ->
      iterations := !iterations - 1;
      c
    | _, _ ->
      let c' = S.step c in
      enqueue wls c'.bp;
      eval_loop { c' with bp = [] } wls

  let rec find_sat_pc pcs =
    if L.is_empty pcs then None
    else
      let pc, node = L.pop pcs in
      debug2 "Checking formula:@\n %a@." Expr.pp pc;
      match Batch.check solver [ pc ] with
      | `Sat -> Some (pc, Execution_tree.find node)
      | `Unsat -> find_sat_pc pcs
      | `Unknown -> assert false

  let rec find_sat_cp cps =
    if L.is_empty cps then None
    else
      let cp = L.pop cps in
      match Batch.check solver [ !cp.pc ] with
      | `Sat -> Some (!cp.pc, Some cp)
      | `Unsat -> find_sat_cp cps
      | `Unknown -> assert false

  let find_sat_path (pcs, cps) =
    match find_sat_cp cps with None -> find_sat_pc pcs | Some _ as cp -> cp

  let invoke (c : config) testsuite =
    let glob0 = Globals.copy c.glob
    and code0 = c.code
    and mem0 = Heap.memcpy c.mem in
    let pc_wl = L.create ()
    and cp_wl = L.create () in
    (* Main concolic loop *)
    let rec concolic_loop c =
      iterations := !iterations + 1;
      let { code; store; bp; _ } = eval_loop c (pc_wl, cp_wl) in
      enqueue (pc_wl, cp_wl) bp;
      match code with
      | _, { it = Interrupt i; at } :: _ ->
        let model = Store.to_json store in
        Fmt.epr "%a!@\nModel:@\n%s@." pp_interruption i model;
        Common.write_test_case testsuite ~witness:true model;
        Some (Fmt.str "%a" pp_interruption i, at)
      | vs, { it = Restart pc; _ } :: es
        when match Batch.check solver [ pc ] with `Sat -> true | _ -> false ->
        let tree', _ = Execution_tree.move_true !(c.tree) in
        c.tree := tree';
        concolic_loop (update c (vs, es) pc (Store.get_key_types store))
      | _, { it = Trapping msg; at } :: _ -> (
        Fmt.epr "%s: %s@." (Source.string_of_region at) msg;
        match find_sat_path (pc_wl, cp_wl) with
        | None -> None
        | Some (_, None) -> concolic_loop (reset c glob0 code0 mem0)
        | Some (pc', Some cp) ->
          let _, c' = clone !cp in
          concolic_loop (update c' c'.code c'.pc (Expr.get_symbols [ pc' ])) )
      | _ -> (
        Common.write_test_case testsuite (Store.to_json store);
        match find_sat_path (pc_wl, cp_wl) with
        | None -> None
        | Some (_, None) -> concolic_loop (reset c glob0 code0 mem0)
        | Some (pc', Some cp) ->
          let _, c' = clone !cp in
          concolic_loop (update c' c'.code c'.pc (Expr.get_symbols [ pc' ])) )
    in
    concolic_loop c

  let s_invoke (c : config) testsuite : (string * Source.region) option =
    let _, c0 = clone c in
    let wl = L.create () in
    let rec eval (c : config) : config =
      match c.code with
      | _, [] -> c
      | _, { it = Trapping msg; at } :: _ -> Trap.error at msg
      | _, { it = Restart _; _ } :: _ -> c
      | _, { it = Interrupt _; _ } :: _ -> c
      | _, _ ->
        let c' = S.step c in
        List.iter
          (fun bp ->
            let pc =
              match bp with
              | Checkpoint cp -> !cp.pc
              | Branchpoint (pc, _) -> pc
            in
            L.push pc wl )
          c'.bp;
        eval { c' with bp = [] }
    in
    let rec find_sat_pc pcs =
      if L.is_empty pcs then false
      else
        (* FIXME: Don't we lose this pc? *)
        match Batch.check solver [ L.pop pcs ] with
        | `Sat -> true
        | `Unsat | `Unknown -> find_sat_pc pcs
    in
    (* Main concolic loop *)
    let rec loop (c : config) =
      iterations := !iterations + 1;
      let { code; store; bp; _ } = eval c in
      List.iter
        (fun bp ->
          let pc =
            match bp with Checkpoint cp -> !cp.pc | Branchpoint (pc, _) -> pc
          in
          L.push pc wl )
        bp;
      match code with
      | _, { it = Interrupt i; at } :: _ ->
        Common.write_test_case testsuite ~witness:true (Store.to_json store);
        Some (Fmt.str "%a" pp_interruption i, at)
      | vs, { it = Restart pc; _ } :: es -> (
        print_endline "--- attempting restart ---";
        iterations := !iterations - 1;
        match Batch.check solver [ pc ] with
        | `Sat -> loop (update c (vs, es) pc (Store.get_key_types store))
        | `Unsat | `Unknown ->
          if L.is_empty wl || not (find_sat_pc wl) then None
          else
            let _, c' = clone c0 in
            loop (s_reset c') )
      | _ ->
        Common.write_test_case testsuite (Store.to_json store);
        if L.is_empty wl || not (find_sat_pc wl) then None
        else
          let _, c' = clone c0 in
          loop (s_reset c')
    in
    let error = loop c in
    error

  let p_invoke (c : config) testsuite : (Expr.t, string * Source.region) result
      =
    let rec eval (c : config) : config =
      match c.code with
      | _, [] -> c
      | _, { it = Trapping msg; at } :: _ -> Trap.error at msg
      | _, { it = Restart _; _ } :: _ ->
        c (* TODO: probably need to change this *)
      | _, { it = Interrupt _; _ } :: _ -> c
      | _, _ ->
        let c' = S.step c in
        eval c'
    in
    let c' = eval c in
    let res =
      match c'.code with
      | _, { it = Interrupt i; at } :: _ ->
        Common.write_test_case testsuite ~witness:true (Store.to_json c'.store);
        Result.error (Fmt.str "%a" pp_interruption i, at)
      | _ ->
        Common.write_test_case testsuite (Store.to_json c'.store);
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
module RND = Guided_search (Common.RandArray) (NoCheckpointStepper)

let exiter _ =
  let loop_time = Sys.time () -. !loop_start in
  write_report None loop_time;
  exit 0

let set_timeout (time_limit : int) : unit =
  if time_limit > 0 then (
    Sys.(set_signal sigalrm (Signal_handle exiter));
    ignore (Unix.alarm time_limit) )

let main testsuite policy (func : Instance.func_inst) (vs : value list)
  (inst : Instance.module_inst) (mem0 : Heap.t) =
  let open Interpreter in
  set_timeout !Flags.timeout;
  let at =
    match func with Func.AstFunc (_, _, f) -> f.at | _ -> Source.no_region
  in
  let glob =
    Globals.of_seq
      (Seq.mapi
         (fun i a ->
           let v = Global.load a in
           ( Int32.of_int i
           , (Evaluations.of_value v, Expr.value (Num (Evaluations.of_value v)))
           ) )
         (List.to_seq inst.globals) )
  in
  let c =
    config Instance.empty_module_inst (List.rev vs)
      Source.[ Invoke func @@ at ]
      mem0 glob (ref head)
  in
  let invoke =
    match policy with
    | Depth -> DFS.invoke
    | Breadth -> BFS.invoke
    | Random -> RND.invoke
  in
  ( if !Interpreter.Flags.log then
      let get_finished () : int = !iterations in
      Common.logger logs get_finished exiter loop_start );
  loop_start := Sys.time ();
  let error = invoke c testsuite in
  write_report error (Sys.time () -. !loop_start);
  (* TODO: Propagate error out *)
  Fmt.pr "Completed paths: %d@\n" !iterations;
  match error with
  | None -> Fmt.pr "All Ok@."
  | Some _bug -> Fmt.pr "Found Problem!@."

let i32 (v : Interpreter.Values.value) at =
  match v with
  | Interpreter.Values.I32 i -> i
  | _ -> Crash.error at "type error: i32 value expected"

let create_func inst f =
  let open Ast in
  let open Source in
  Interpreter.Func.alloc (type_ inst f.it.ftype) (ref inst) f

let create_table _ tab =
  let open Ast in
  let open Source in
  let { ttype } = tab.it in
  Interpreter.Table.alloc ttype

let create_memory _ mem =
  let open Ast in
  let open Source in
  let { mtype } = mem.it in
  Interpreter.Memory.alloc mtype

let create_global inst glob =
  let open Ast in
  let open Source in
  let { gtype; value } = glob.it in
  let v = Interpreter.Eval.eval_const inst value in
  Interpreter.Global.alloc gtype v

let create_export inst ex =
  let open Ast in
  let open Source in
  let open Instance in
  let { name; edesc } = ex.it in
  let ext =
    match edesc.it with
    | FuncExport x -> ExternFunc (func inst x)
    | TableExport x -> ExternTable (table inst x)
    | MemoryExport x -> ExternMemory (memory inst x)
    | GlobalExport x -> ExternGlobal (global inst x)
  in
  (name, ext)

let init_func inst func =
  match func with
  | Interpreter.Func.AstFunc (_, inst_ref, _) -> inst_ref := inst
  | _ -> assert false

let init_table inst seg =
  let open Ast in
  let open Interpreter in
  let open Source in
  let { index; offset = const; init } = seg.it in
  let tab = table inst index in
  let offset = i32 (Eval.eval_const inst const) const.at in
  let end_ = Int32.(add offset (of_int (List.length init))) in
  let bound = Table.size tab in
  if I32.lt_u bound end_ || I32.lt_u end_ offset then
    Common.Link.error seg.at "elements segment does not fit table";
  fun () ->
    Table.blit tab offset
      (List.map (fun x -> Instance.FuncElem (func inst x)) init)

let init_memory inst sym_mem seg =
  let open Ast in
  let open Interpreter in
  let open Source in
  let { index; offset = const; init } = seg.it in
  let mem = memory inst index in
  let offset' = i32 (Eval.eval_const inst const) const.at in
  let offset = I64_convert.extend_i32_u offset' in
  let end_ = Int64.(add offset (of_int (String.length init))) in
  let bound = Memory.bound mem in
  if I64.lt_u bound end_ || I64.lt_u end_ offset then
    Common.Link.error seg.at "data segment does not fit memory";
  fun () -> Heap.store_bytes sym_mem offset init

let add_import m ext im inst =
  let open Interpreter in
  let open Instance in
  if not (Types.match_extern_type (extern_type_of ext) (Ast.import_type m im))
  then Common.Link.error im.Source.at "incompatible import type";
  match ext with
  | ExternFunc func -> { inst with funcs = func :: inst.funcs }
  | ExternTable tab -> { inst with tables = tab :: inst.tables }
  | ExternMemory mem -> { inst with memories = mem :: inst.memories }
  | ExternGlobal glob -> { inst with globals = glob :: inst.globals }

let init m exts testsuite policy =
  let open Ast in
  let open Interpreter in
  let open Source in
  let { imports
      ; tables
      ; memories
      ; globals
      ; funcs
      ; types
      ; exports
      ; elems
      ; data
      ; start
      } =
    m.it
  in
  if List.length exts <> List.length imports then
    Common.Link.error m.at "wrong number of imports provided for initialisation";
  let inst0 =
    { (List.fold_right2 (add_import m) exts imports Instance.empty_module_inst) with
      types = List.map (fun type_ -> type_.it) types
    }
  in
  let fs = List.map (create_func inst0) funcs in
  let inst1 =
    { inst0 with
      funcs = inst0.funcs @ fs
    ; tables = inst0.tables @ List.map (create_table inst0) tables
    ; memories = inst0.memories @ List.map (create_memory inst0) memories
    ; globals = inst0.globals @ List.map (create_global inst0) globals
    }
  in
  let inst = { inst1 with exports = List.map (create_export inst1) exports } in
  List.iter (init_func inst) fs;
  let init_elems = List.map (init_table inst) elems in
  let memory = Heap.alloc Flags.hashtbl_default_size in
  let init_datas = List.map (init_memory inst memory) data in
  List.iter (fun f -> f ()) init_elems;
  List.iter (fun f -> f ()) init_datas;
  Option.iter
    (fun x -> ignore (main testsuite policy (func inst x) [] inst memory))
    start;
  (memory, inst)
