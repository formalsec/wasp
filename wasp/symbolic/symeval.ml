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


type policy = Random | Depth | Breadth (*| Coverage *)

type bug =
  | Overflow
  | UAF
  | InvalidFree

type interruption =
  | IntLimit
  | AssFail of path_conditions
  | AsmFail of path_conditions
  | Bug of bug

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

type path_cond =
{
  branches : path_conditions;
  assumptions : path_conditions;
}

(* Symbolic configuration  *)
type sym_config =
{
  sym_frame  : sym_frame;
  sym_code   : sym_code;
  logic_env  : Logicenv.t;
  path_cond  : path_cond;
  sym_mem    : Symmem2.t;
  sym_budget : int;  (* to model stack overflow *)
}

(* Symbolic frame and configuration  *)
let path_cond branches assumptions = {branches; assumptions}
let sym_frame sym_inst sym_locals = {sym_inst; sym_locals}
let sym_config inst vs es sym_m = {
  sym_frame  = sym_frame inst [];
  sym_code   = vs, es;
  logic_env  = Logicenv.create [];
  path_cond  = path_cond [] [];
  sym_mem    = sym_m;
  sym_budget = 100000 (* models default recursion limit in a system *)
}

exception InstrLimit of sym_config
exception AssumeFail of sym_config * path_conditions
exception AssertFail of sym_config * region
exception BugException of sym_config * region * bug
exception Unsatisfiable

let lines_to_ignore = ref 0

let step_cnt   = ref 0
let solver_cnt = ref 0
let iterations = ref 0
let incomplete = ref false

(* Time statistics *)
let solver_time = ref 0.
let loop_start = ref 0.


(* Helpers *)
let debug str = if !Flags.trace then print_endline str

(* Generic counter *)
let count (init : int) : (unit -> int)=
  let next = ref init in
  let next () =
    let n = !next in
    next := n + 1;
    n
  in next

let parse_policy (p : string) : policy option =
  match p with
  | "random"   -> Some Random
  | "depth"    -> Some Depth
  | "breadth"  -> Some Breadth
  (*| "coverage" -> Some Coverage *)
  | _          -> None

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

let timed_check_sat formulas =
  let start = Sys.time () in
  let opt_model = Z3Encoding2.check_sat_core formulas in
  let delta = (Sys.time ()) -. start in
  solver_time := !solver_time +. delta;
  solver_cnt := !solver_cnt + 1;
  opt_model

let get_reason error : string =
  let type_str, r = error in
  let region_str = Source.string_of_pos r.left ^
    (if r.right = r.left then ""
                         else "-" ^ string_of_pos r.right) in
  "{" ^
    "\"type\" : \"" ^ type_str ^ "\", " ^
    "\"line\" : \"" ^ region_str ^ "\"" ^
  "}"

let write_test_case out_dir test_data is_witness cnt : unit =
  if not (test_data = "[]") then (
    let i = cnt () in
    let filename =
      if is_witness then Printf.sprintf "%s/witness_%05d.json" out_dir i
      else Printf.sprintf "%s/test_%05d.json" out_dir i
    in Io.save_file filename test_data
  )

let write_report spec reason witness coverage loop_time : unit =
  let report_str = "{" ^
    "\"specification\": "        ^ (string_of_bool spec)          ^ ", " ^
    "\"reason\" : "              ^ reason                         ^ ", " ^
    "\"coverage\" : \""          ^ (string_of_float coverage)     ^ "\", " ^
    "\"loop_time\" : \""         ^ (string_of_float loop_time)    ^ "\", " ^
    "\"solver_time\" : \""       ^ (string_of_float !solver_time) ^ "\", " ^
    "\"paths_explored\" : "      ^ (string_of_int !iterations)    ^ ", " ^
    "\"solver_counter\" : "      ^ (string_of_int !solver_cnt)    ^ ", " ^
    "\"instruction_counter\" : " ^ (string_of_int !step_cnt)      ^ ", " ^
    "\"incomplete\" : "          ^ (string_of_bool !incomplete)   ^
  "}"
  in Io.save_file (Filename.concat !Flags.output "report.json") report_str

let set_timeout (time_limit : int) : unit =
  let alarm_handler i : unit =
    Z3Encoding2.interrupt_z3 ();
    incomplete := true;
    let loop_time = (Sys.time ()) -. !loop_start in
    write_report true "{}" "[]" 0.0 loop_time;
    exit 0
  in
  if time_limit > 0 then (
    Sys.(set_signal sigalrm (Signal_handle alarm_handler));
    ignore (Unix.alarm time_limit)
  )

let update_config model lenv c inst mem glob code chk_tbl =
  let li32 = Logicenv.get_vars_by_type I32Type lenv
  and li64 = Logicenv.get_vars_by_type I64Type lenv
  and lf32 = Logicenv.get_vars_by_type F32Type lenv
  and lf64 = Logicenv.get_vars_by_type F64Type lenv in
  let binds = Z3Encoding2.lift_z3_model model li32 li64 lf32 lf64 in
  Hashtbl.reset chk_tbl;
  Logicenv.reset lenv;
  Logicenv.init lenv binds;
  Symmem2.clear c.sym_mem;
  Symmem2.init c.sym_mem mem;
  Instance.set_globals !inst glob;
  {c with sym_budget=100000; sym_code=code; path_cond=path_cond [] []}

let rec eval
    (c : sym_config)
    (stepper : sym_config -> sym_config) : sym_config =
  match c.sym_code with
  | vs, [] ->
    c

  | vs, {it = STrapping msg; at} :: _ ->
    Trap.error at msg

  | vs, {it = Interrupt i; at} :: es ->
    let exn = match i with
      | IntLimit   -> InstrLimit c
      | AsmFail pc -> AssumeFail ({c with sym_code = vs, es}, pc)
      | AssFail pc -> AssertFail (c, at)
      | Bug b      -> BugException (c, at, b)
    in raise exn

  | vs, es ->
    eval (stepper c) stepper

module PQueue =
struct
  type 'a order = 'a -> 'a -> int

  type 'a t = {
    mutable     size : int;
    mutable capacity : int;
    mutable     heap : 'a array;
               order : 'a order;
  }

  exception Empty

  let make order =
    { size = 0; capacity = 8; heap = Array.make 8 (Obj.magic 0); order = order }

  let create () =
    { size = 0; capacity = 8; heap = Array.make 8 (Obj.magic 0); order = compare }

  let length h = h.size

  let is_empty h = h.size = 0

  let expand_capacity h =
    let capacity' = min (h.capacity * 2) Sys.max_array_length in
    if h.size = capacity' then failwith "maximum capacity reached";
    let heap' = Array.make capacity' (Obj.magic 0) in
    Array.blit h.heap 0 heap' 0 h.size;
    h.heap <- heap';
    h.capacity <- capacity'

  let parent i = (i - 1) / 2
  let left   i = 2 * i + 1
  let right  i = 2 * i + 2

  let push x h =
    let i = length h in
    if i = h.capacity then expand_capacity h;
    h.heap.(i)  <- x;
    h.size <- i + 1;
    let rec moveup i =
      let ord = h.order in
      let pi = parent i in
      if i <> 0 && ord h.heap.(pi) x < 0 then (
        let tmp = h.heap.(i) in
        h.heap.(i) <- h.heap.(pi);
        h.heap.(pi) <- tmp;
        moveup pi
      )
    in moveup i

  let top h =
    if length h = 0 then raise Empty;
    h.heap.(0)

  let pop h =
    let n = length h in
    if n = 0 then raise Empty;
    let m = h.heap.(0) in
    h.heap.(0) <- h.heap.(n - 1);
    h.heap.(n - 1) <- m;
    h.size <- n - 1;
    let rec heapify i =
      let ord = h.order in
      let li = left i in
      let ri = right i in
      if h.size > 1 && li < h.size && ri < h.size then (
        let i' = if ord h.heap.(ri) h.heap.(li) > 0 then ri else li
        in
        if ord h.heap.(i') h.heap.(i) > 0 then (
          let tmp = h.heap.(i) in
          h.heap.(i) <- h.heap.(i');
          h.heap.(i') <- tmp;
          heapify i'
        )
      )
    in heapify 0;
    m
end

module type Paths =
sig
  type 'a t
  exception Empty
  val create : unit -> 'a t
  val pop : 'a t -> 'a
  val push : 'a -> 'a t -> unit
  val is_empty : 'a t -> bool
end

module RandomSearch =
struct

  (* Tracks malloc chunks (loc, size) *)
  let chk_tbl = Hashtbl.create 512

  let rec step (c : sym_config) : sym_config =
    step_cnt := !step_cnt + 1;
    let {
      sym_frame = frame;
      sym_code  = vs, es;
      logic_env = logic_env;
      path_cond = pc;
      sym_mem   = mem;
      _
    } = c in
    let e = List.hd es in
    Coverage.record_line (Source.get_line e.at);
    let vs', es', logic_env', pc', mem' =
      if (not (!Flags.inst_limit = -1)) && (!step_cnt >= !Flags.inst_limit) then (
        incomplete := true;
        vs, [Interrupt IntLimit @@ e.at], logic_env, pc, mem
      ) else (match e.it, vs with
      | SPlain e', vs ->
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
          let pc' = { pc with branches = add_constraint ~neg:true ex pc.branches } in
          vs', [SPlain (Block (ts, es2)) @@ e.at], logic_env, pc', mem

        | If (ts, es1, es2), (I32 i, ex) :: vs' ->
          let pc' = { pc with branches = add_constraint ex pc.branches } in
          vs', [SPlain (Block (ts, es1)) @@ e.at], logic_env, pc', mem

        | Br x, vs ->
          [], [SBreaking (x.it, vs) @@ e.at], logic_env, pc, mem

        | BrIf x, (I32 0l, ex) :: vs' ->
          let pc' = { pc with branches = add_constraint ~neg:true ex pc.branches } in
          vs', [], logic_env, pc', mem

        | BrIf x, (I32 i, ex) :: vs' ->
          let pc' = { pc with branches = add_constraint ex pc.branches } in
          vs', [SPlain (Br x) @@ e.at], logic_env, pc', mem

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
          let pc' = { pc with branches = add_constraint ~neg:true ex pc.branches } in
          v2 :: vs', [], logic_env, pc', mem

        | Select, (I32 i, ex) :: v2 :: v1 :: vs' ->
          let pc' = { pc with branches = add_constraint ex pc.branches } in
          v1 :: vs', [], logic_env, pc', mem

        | LocalGet x, vs ->
          !(local frame x) :: vs, [], logic_env, pc, mem

        | LocalSet x, (v, ex) :: vs' ->
          local frame x := (v, simplify ex);
          vs', [], logic_env, pc, mem

        | LocalTee x, (v, ex) :: vs' ->
          let ex' = simplify ex in
          local frame x := (v, ex');
          (v, ex') :: vs', [], logic_env, pc, mem

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
              let chunk_size =
                try Hashtbl.find chk_tbl low
                with Not_found -> raise (BugException (c, e.at, UAF)) in
              let high = Int64.(add (of_int32 low) (of_int32 chunk_size))
              and ptr_val = Int64.(add base (of_int32 offset)) in
              (* ptr_val \notin [low, high[ => overflow *)
              if ptr_val < (Int64.of_int32 low) || ptr_val >= high then
                raise (BugException (c, e.at, Overflow))
            end;
            let (v, e) =
              match sz with
              | None           -> Symmem2.load_value mem base offset ty
              | Some (sz, ext) -> Symmem2.load_packed sz ext mem base offset ty
            in
            (*print_endline ("after load: " ^ (Symvalue.to_string e));*)
            (v, e) :: vs', [], logic_env, pc, mem
          with
          | BugException (_, at, b) ->
            vs', [Interrupt (Bug b) @@ e.at], logic_env, pc, mem
          | exn ->
            vs', [STrapping (memory_error e.at exn) @@ e.at], logic_env, pc, mem
          end

        | Store {offset; sz; _}, (v, ex) :: (I32 i, sym_ptr) :: vs' ->
          let base = I64_convert.extend_i32_u i in
          let ptr = get_ptr (simplify sym_ptr) in
          begin try
            if Option.is_some ptr then begin
              let low = I32Value.of_value (Option.get ptr) in
              let chunk_size =
                try Hashtbl.find chk_tbl low
                with Not_found -> raise (BugException (c, e.at, UAF)) in
              let high = Int64.(add (of_int32 low) (of_int32 chunk_size))
              and ptr_val = Int64.(add base (of_int32 offset)) in
              if (Int64.of_int32 low) > ptr_val || ptr_val >= high then
                raise (BugException (c, e.at, Overflow))
            end;
            begin match sz with
            | None    -> Symmem2.store_value mem base offset (v, simplify ex)
            | Some sz -> Symmem2.store_packed sz mem base offset (v, simplify ex)
            end;
            vs', [], logic_env, pc, mem
          with
          | BugException (_, at, b) ->
            vs', [Interrupt (Bug b) @@ e.at], logic_env, pc, mem
          | exn ->
            vs', [STrapping (memory_error e.at exn) @@ e.at], logic_env, pc, mem
          end

        | MemorySize, vs ->
          let mem' = memory frame.sym_inst (0l @@ e.at) in
          let v = I32 (Memory.size mem') in
          (v, Value v) :: vs, [], logic_env, pc, mem

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
          vs', [Interrupt (AssFail pc.branches) @@ e.at], logic_env, pc, mem

        | SymAssert, (I32 i, ex) :: vs' -> (* != 0 on top of stack *)
          debug ">>> Assert reached. Checking satisfiability...";
          let es' =
            if is_concrete (simplify ex) then []
            else (
              let formulas = pc.assumptions @ (add_constraint ~neg:true ex pc.branches) in
              match timed_check_sat (Formula.to_formulas formulas) with
              | None   -> []
              | Some m ->
                let li32 = Logicenv.get_vars_by_type I32Type logic_env
                and li64 = Logicenv.get_vars_by_type I64Type logic_env
                and lf32 = Logicenv.get_vars_by_type F32Type logic_env
                and lf64 = Logicenv.get_vars_by_type F64Type logic_env in
                let binds = Z3Encoding2.lift_z3_model m li32 li64 lf32 lf64 in
                Logicenv.update logic_env binds;
                [Interrupt (AssFail pc.branches) @@ e.at]
            )
          in if es' = [] then
            debug "\n\n###### Assertion passed ######";
          vs', es', logic_env, pc, mem

        | SymAssume, (I32 0l, ex) :: vs' ->
          debug (">>> Assumed false {line> " ^ (Source.string_of_pos e.at.left) ^
            "}. Finishing...");
          if (not !Flags.smt_assume) || is_concrete (simplify ex) then (
            let pc' = { pc with branches = add_constraint ~neg:true ex pc.branches } in
            vs', [Interrupt (AsmFail pc'.branches) @@ e.at], logic_env, pc', mem
          ) else (
            let pc' = pc.assumptions @ (add_constraint ex pc.branches) in
            let formulas = Formula.to_formulas pc' in
            let vs'', es', pc'' = match timed_check_sat formulas with
              | None ->
                let pc_fls = { pc with branches = add_constraint ~neg:true ex pc.branches } in
                vs', [Interrupt (AsmFail pc') @@ e.at], pc_fls
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
                List.map f vs', [], {pc with branches = pc'}
            in vs'', es', logic_env, pc'', mem)

        | SymAssume, (I32 i, ex) :: vs' ->
          debug ">>> Assume passed. Continuing execution...";
          let pc' = { pc with branches = add_constraint ex pc.branches } in
          vs', [], logic_env, pc', mem

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
            Hashtbl.add chk_tbl b a;
            (I32 b, Ptr (I32 b)) :: vs', [], logic_env, pc, mem

        | Free, (I32 i, _) :: vs' ->
          let es' =
            if not (Hashtbl.mem chk_tbl i) then (
              [Interrupt (Bug InvalidFree) @@ e.at]
            ) else (
              Hashtbl.remove chk_tbl i;
              []
            )
          in vs', es', logic_env, pc, mem

        (* Deprecated *)
        | SymInt32 x, vs' ->
          let v =
            try Logicenv.find logic_env x with
            | Not_found ->
              let v' = I32 (I32.rand 1000) in
              Logicenv.add logic_env x v';
              v'
          in (v, Symvalue.Symbolic (SymInt32, x)) :: vs', [], logic_env, pc, mem

        (* Deprecated *)
        | SymInt64 x, vs' ->
          let v =
            try Logicenv.find logic_env x with
            | Not_found ->
              let v' = I64 (I64.rand 1000) in
              Logicenv.add logic_env x v';
              v'
          in (v, Symvalue.Symbolic (SymInt64, x)) :: vs', [], logic_env, pc, mem

        (* Deprecated *)
        | SymFloat32 x, vs' ->
          let v =
            try Logicenv.find logic_env x with
            | Not_found ->
              let v' = F32 (F32.rand 1000.0) in
              Logicenv.add logic_env x v';
              v'
          in (v, Symvalue.Symbolic (SymFloat32, x)) :: vs', [], logic_env, pc, mem

        (* Deprecated *)
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

        | TernaryOp, (I32 r2, s_r2) :: (I32 r1, s_r1) :: (I32 c, s_c) :: vs' ->
          let r = I32 (if c = 0l then r2 else r1) in
          let s_c' = to_constraint (simplify s_c) in
          let v, asm =
            begin match s_c' with
            | None -> (r, if c = 0l then s_r2 else s_r1), pc.assumptions
            | Some s ->
              let x = Logicenv.next logic_env "__ternary" in
              Logicenv.add logic_env x r;
              let s_x = to_symbolic I32Type x in
              let t_eq  = I32Relop (I32Eq, s_x, s_r1) in
              let t_imp = I32Binop (I32Or, negate_relop s, t_eq) in
              let f_eq  = I32Relop (I32Eq, s_x, s_r2) in
              let f_imp = I32Binop (I32Or, s, f_eq) in
              let cond  = I32Binop (I32And, t_imp, f_imp) in
              (r, s_x), I32Relop (I32Ne, cond, Value (I32 0l)) :: pc.assumptions
            end
          in v :: vs', [], logic_env, { pc with assumptions = asm }, mem

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

        | SetPriority, _ :: _  :: _ :: vs' ->
          vs', [], logic_env, pc, mem

        | PopPriority, _ :: vs' ->
          vs', [], logic_env, pc, mem

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
        let c' = step {c with sym_code = code'} in
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
        let c' = step {
          sym_frame = frame';
          sym_code = code';
          logic_env = c.logic_env;
          path_cond = c.path_cond;
          sym_mem = c.sym_mem;
          sym_budget = c.sym_budget - 1
        }
        in vs, [SFrame (n, c'.sym_frame, c'.sym_code) @@ e.at], c'.logic_env, c'.path_cond, c'.sym_mem

      | SInvoke func, vs when c.sym_budget = 0 ->
        Exhaustion.error e.at "call stack exhausted"

      | SInvoke func, vs ->
        let symbolic_arg t =
          let x = Logicenv.next logic_env "arg" in
          let v = Logicenv.get logic_env x t false in
          (v, to_symbolic t x)
        in
        let FuncType (ins, out) = Func.type_of func in
        let n = List.length ins in
        let vs =
          if n > 0 && (List.length vs) = 0 then
            List.map (fun t -> symbolic_arg t) ins
          else vs
        in
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
    in
    { c with sym_code = vs', es' @ List.tl es; logic_env = logic_env';
             path_cond = pc'; sym_mem = mem' }

  let run
      (conf : sym_config ref)
      (inst : module_inst ref)
      (test_suite : string) =
    let module PCMap = Map.Make(String) in
    let test_cnt = count 1
    and ini_mem  = Symmem2.to_list !inst.sym_memory
    and ini_glob = Global.contents !inst.globals
    and ini_code = !conf.sym_code
    and assume_fails = Constraints.create
    and finish = ref false and error = ref None in
    let rec loop c global_pc =
      if !Flags.trace then ((* Debug *)
        let curly = String.make 35 '~' in
        Printf.printf "%s ITERATION NUMBER %03d %s\n\n"
          curly (!iterations + 1) curly
      );
      iterations := !iterations + 1;
      let {logic_env; path_cond = pc; _} = try eval c step with
        | InstrLimit c'            -> finish:= true; c'
        | AssumeFail (c', pc)      ->
            iterations := !iterations - 1;
            Constraints.add assume_fails !iterations pc; c'
        | AssertFail (c', at)      -> error := Some ("Assertion Failure", at); c'
        | BugException (c', at, b) -> error := Some (string_of_bug b, at); c'
        | e -> raise e
      in
      let testcase = Logicenv.(to_json (to_list logic_env)) in
      write_test_case test_suite testcase (Option.is_some !error) test_cnt;
      if Option.is_some !error then (
        incomplete := true;
        false, get_reason (Option.get !error), testcase
      ) else if !finish || (!iterations = 1 && pc.branches = []) then (
        true, "{}", "[]"
      ) else (
        let pc' = if pc.branches <> [] then Formula.(negate (to_formula pc.branches))
                                       else Formula.True in
        let asm' = if pc.assumptions <> [] then Formula.to_formula pc.assumptions
                                           else Formula.True in
        let global_pc' = PCMap.add (Formula.to_string asm') asm' global_pc |>
          PCMap.add (Formula.to_string pc') pc' in
        let formulas = List.map (fun (_, f) -> f) (PCMap.bindings global_pc') in
        if !Flags.trace then ((* Debug *)
          let delim = String.make 6 '$' in
          let formula = Formula.conjunct formulas in
          Printf.printf "\n\n%s LOGICAL ENVIRONMENT BEFORE Z3 STATE %s\n%s%s\n\n"
            delim delim (Logicenv.to_string logic_env) (String.make 48 '$');
          Printf.printf "\n\n%s PATH CONDITIONS BEFORE Z3 %s\n%s\n%s\n"
            delim delim (pp_string_of_pc pc.branches) (String.make 38 '$');
          Printf.printf "\n\n%s GLOBAL PATH CONDITION %s\n%s\n%s\n\n"
            delim delim (Formula.pp_to_string formula) (String.make 28 '$');
        );
        let prev_time = !solver_time in
        match timed_check_sat formulas with
        | None   -> true, "{}", "[]"
        | Some m ->
            let c' = update_config m logic_env c inst ini_mem ini_glob ini_code chk_tbl in
            if !Flags.trace then ((* Debug *)
              let delim = String.make 6 '$' in
              let formula = Formula.conjunct formulas in
              Printf.printf "SATISFIABLE\nMODEL:\n%s\n"
                (Z3.Model.to_string m);
              Printf.printf "\n\n%s NEW LOGICAL ENV STATE %s\n%s%s\n\n"
                delim delim (Logicenv.to_string logic_env) (String.make 28 '$');
              Printf.printf "\n%s ITERATION %03d STATISTICS: %s\n"
                (String.make 23 '-') !iterations (String.make 23 '-');
              Printf.printf "PC SIZE: %d\n" (Formula.length pc');
              Printf.printf "GLOBAL PC SIZE: %d\n" (Formula.length formula);
              Printf.printf "TIME TO SOLVE GLOBAL PC: %f\n"
                (!solver_time -. prev_time);
              Printf.printf "%s\n\n\n%s\n\n"
                (String.make 73 '-') (String.make 92 '~');
            );
            loop c' global_pc'
      )
    in
    loop_start := Sys.time ();
    let spec, reason, witness =
      PCMap.add "True" Formula.True PCMap.empty |> loop !conf in
    let loop_time = (Sys.time ()) -. !loop_start in
    let n_lines = List.((length !inst.types) + (length !inst.tables) +
                        (length !inst.memories) + (length !inst.globals) +
                        (length !inst.exports) + 1) in
    let coverage = (Coverage.calculate_cov inst (n_lines + !lines_to_ignore)) *. 100.0 in
    write_report spec reason witness coverage loop_time;
    !conf.sym_code

end

module GuidedSearch (X : Paths) =
struct
  type tree =
    | Leaf
    | Node of tree ref * tree ref

  (* Execution tracing *)
  let head = ref Leaf
  let tree = ref head
  let to_explore = X.create ()

  (* Tracks malloc chunks (loc, size) *)
  let chk_tbl = Hashtbl.create 512

  let move_true (t : tree ref) : tree ref * bool =
    match !t with
    | Leaf ->
      let rt = ref Leaf and rf = ref Leaf in
      t := Node (rt, rf);
      rt, true
    | Node (rt, rf) -> rt, false

  let move_false (t : tree ref) : tree ref * bool =
    match !t with
    | Leaf ->
      let rt = ref Leaf and rf = ref Leaf in
      t := Node (rt, rf);
      rf, true
    | Node (rt, rf) -> rf, false

  let branch_on_cond bval c pc : unit =
    let c' = simplify c in
    if not (is_concrete c') then (
      let tree', to_branch = if bval then move_true !tree
                                     else move_false !tree in
      tree := tree';
      let pc' = pc.assumptions @ pc.branches in
      if to_branch then X.push (add_constraint ~neg:bval c pc') to_explore
    )

  (*  Symbolic step  *)
  let rec step (c : sym_config) : sym_config =
    step_cnt := !step_cnt + 1;
    let {
      sym_frame = frame;
      sym_code  = vs, es;
      logic_env = logic_env;
      path_cond = pc;
      sym_mem   = mem;
      _
    } = c in
    let e = List.hd es in
    Coverage.record_line (Source.get_line e.at);
    let vs', es', logic_env', pc', mem' =
      if (not (!Flags.inst_limit = -1)) && (!step_cnt >= !Flags.inst_limit) then (
        incomplete := true;
        vs, [Interrupt IntLimit @@ e.at], logic_env, pc, mem
      ) else (match e.it, vs with
      | SPlain e', vs ->
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
          let _ = branch_on_cond false ex pc in
          let pc' = { pc with branches = add_constraint ~neg:true ex pc.branches } in
          vs', [SPlain (Block (ts, es2)) @@ e.at], logic_env, pc', mem

        | If (ts, es1, es2), (I32 i, ex) :: vs' ->
          let _ = branch_on_cond true ex pc in
          let pc' = { pc with branches = add_constraint ex pc.branches } in
          vs', [SPlain (Block (ts, es1)) @@ e.at], logic_env, pc', mem

        | Br x, vs ->
          [], [SBreaking (x.it, vs) @@ e.at], logic_env, pc, mem

        | BrIf x, (I32 0l, ex) :: vs' ->
          let _ = branch_on_cond false ex pc in
          let pc' = { pc with branches = add_constraint ~neg:true ex pc.branches } in
          vs', [], logic_env, pc', mem

        | BrIf x, (I32 i, ex) :: vs' ->
          let _ = branch_on_cond true ex pc in
          let pc' = { pc with branches = add_constraint ex pc.branches } in
          vs', [SPlain (Br x) @@ e.at], logic_env, pc', mem

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
          let _ = branch_on_cond false ex pc in
          let pc' = { pc with branches = add_constraint ~neg:true ex pc.branches } in
          v2 :: vs', [], logic_env, pc', mem

        | Select, (I32 i, ex) :: v2 :: v1 :: vs' ->
          let _ = branch_on_cond true ex pc in
          let pc' = { pc with branches = add_constraint ex pc.branches } in
          v1 :: vs', [], logic_env, pc', mem

        | LocalGet x, vs ->
          !(local frame x) :: vs, [], logic_env, pc, mem

        | LocalSet x, (v, ex) :: vs' ->
          local frame x := (v, simplify ex);
          vs', [], logic_env, pc, mem

        | LocalTee x, (v, ex) :: vs' ->
          let ex' = simplify ex in
          local frame x := (v, ex');
          (v, ex') :: vs', [], logic_env, pc, mem

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
              let chunk_size =
                try Hashtbl.find chk_tbl low
                with Not_found -> raise (BugException (c, e.at, UAF)) in
              let high = Int64.(add (of_int32 low) (of_int32 chunk_size))
              and ptr_val = Int64.(add base (of_int32 offset)) in
              (* ptr_val \notin [low, high[ => overflow *)
              if ptr_val < (Int64.of_int32 low) || ptr_val >= high then
                raise (BugException (c, e.at, Overflow))
            end;
            let (v, e) =
              match sz with
              | None           -> Symmem2.load_value mem base offset ty
              | Some (sz, ext) -> Symmem2.load_packed sz ext mem base offset ty
            in
            (*print_endline ("after load: " ^ (Symvalue.to_string e));*)
            (v, e) :: vs', [], logic_env, pc, mem
          with
          | BugException (_, at, b) ->
            vs', [Interrupt (Bug b) @@ e.at], logic_env, pc, mem
          | exn ->
            vs', [STrapping (memory_error e.at exn) @@ e.at], logic_env, pc, mem
          end

        | Store {offset; sz; _}, (v, ex) :: (I32 i, sym_ptr) :: vs' ->
          let base = I64_convert.extend_i32_u i in
          let ptr = get_ptr (simplify sym_ptr) in
          begin try
            if Option.is_some ptr then begin
              let low = I32Value.of_value (Option.get ptr) in
              let chunk_size =
                try Hashtbl.find chk_tbl low
                with Not_found -> raise (BugException (c, e.at, UAF)) in
              let high = Int64.(add (of_int32 low) (of_int32 chunk_size))
              and ptr_val = Int64.(add base (of_int32 offset)) in
              if (Int64.of_int32 low) > ptr_val || ptr_val >= high then
                raise (BugException (c, e.at, Overflow))
            end;
            begin match sz with
            | None    -> Symmem2.store_value mem base offset (v, simplify ex)
            | Some sz -> Symmem2.store_packed sz mem base offset (v, simplify ex)
            end;
            vs', [], logic_env, pc, mem
          with
          | BugException (_, at, b) ->
            vs', [Interrupt (Bug b) @@ e.at], logic_env, pc, mem
          | exn ->
            vs', [STrapping (memory_error e.at exn) @@ e.at], logic_env, pc, mem
          end

        | MemorySize, vs ->
          let mem' = memory frame.sym_inst (0l @@ e.at) in
          let v = I32 (Memory.size mem') in
          (v, Value v) :: vs, [], logic_env, pc, mem

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
          vs', [Interrupt (AssFail pc.branches) @@ e.at], logic_env, pc, mem

        | SymAssert, (I32 i, ex) :: vs' -> (* != 0 on top of stack *)
          debug ">>> Assert reached. Checking satisfiability...";
          let es' =
            if is_concrete (simplify ex) then []
            else (
              let formulas = pc.assumptions @ (add_constraint ~neg:true ex pc.branches) in
              match timed_check_sat (Formula.to_formulas formulas) with
              | None   -> []
              | Some m ->
                let li32 = Logicenv.get_vars_by_type I32Type logic_env
                and li64 = Logicenv.get_vars_by_type I64Type logic_env
                and lf32 = Logicenv.get_vars_by_type F32Type logic_env
                and lf64 = Logicenv.get_vars_by_type F64Type logic_env in
                let binds = Z3Encoding2.lift_z3_model m li32 li64 lf32 lf64 in
                Logicenv.update logic_env binds;
                [Interrupt (AssFail pc.branches) @@ e.at]
            )
          in
          if es' = [] then debug "\n\n###### Assertion passed ######";
          vs', es', logic_env, pc, mem

        | SymAssume, (I32 0l, ex) :: vs' ->
          debug (">>> Assumed false {line> " ^ (Source.string_of_pos e.at.left) ^
            "}. Finishing...");
          if (not !Flags.smt_assume) || is_concrete (simplify ex) then (
            let _ = branch_on_cond false ex pc in
            let pc' = { pc with branches = add_constraint ~neg:true ex pc.branches } in
            vs', [Interrupt (AsmFail pc'.branches) @@ e.at], logic_env, pc', mem
          ) else (
            let pc' = pc.assumptions @ (add_constraint ex pc.branches) in
            let formulas = Formula.to_formulas pc' in
            let vs'', es', pc'' = match timed_check_sat formulas with
              | None ->
                let _ = branch_on_cond false ex pc in
                let pc_fls = { pc with branches = add_constraint ~neg:true ex pc.branches } in
                vs', [Interrupt (AsmFail pc') @@ e.at], pc_fls
              | Some m ->
                (* Record path *)
                if not (is_concrete (simplify ex)) then (
                  let tree', _ = move_true !tree in
                  tree := tree'
                );
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
                List.map f vs', [], {pc with branches = pc'}
            in vs'', es', logic_env, pc'', mem)

        | SymAssume, (I32 i, ex) :: vs' ->
          debug ">>> Assume passed. Continuing execution...";
          if not (is_concrete (simplify ex)) then (
            let tree', _ = move_true !tree in
            tree := tree'
          );
          let pc' = { pc with branches = add_constraint ex pc.branches } in
          vs', [], logic_env, pc', mem

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
            Hashtbl.add chk_tbl b a;
            (I32 b, Ptr (I32 b)) :: vs', [], logic_env, pc, mem

        | Free, (I32 i, _) :: vs' ->
          let es' =
            if not (Hashtbl.mem chk_tbl i) then (
              [Interrupt (Bug InvalidFree) @@ e.at]
            ) else (
              Hashtbl.remove chk_tbl i;
              []
            )
          in vs', es', logic_env, pc, mem

        (* Deprecated *)
        | SymInt32 x, vs' ->
          let v =
            try Logicenv.find logic_env x with
            | Not_found ->
              let v' = I32 (I32.rand 1000) in
              Logicenv.add logic_env x v';
              v'
          in (v, Symvalue.Symbolic (SymInt32, x)) :: vs', [], logic_env, pc, mem

        (* Deprecated *)
        | SymInt64 x, vs' ->
          let v =
            try Logicenv.find logic_env x with
            | Not_found ->
              let v' = I64 (I64.rand 1000) in
              Logicenv.add logic_env x v';
              v'
          in (v, Symvalue.Symbolic (SymInt64, x)) :: vs', [], logic_env, pc, mem

        (* Deprecated *)
        | SymFloat32 x, vs' ->
          let v =
            try Logicenv.find logic_env x with
            | Not_found ->
              let v' = F32 (F32.rand 1000.0) in
              Logicenv.add logic_env x v';
              v'
          in (v, Symvalue.Symbolic (SymFloat32, x)) :: vs', [], logic_env, pc, mem

        (* Deprecated *)
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

        | TernaryOp, (I32 r2, s_r2) :: (I32 r1, s_r1) :: (I32 c, s_c) :: vs' ->
          let r = I32 (if c = 0l then r2 else r1) in
          let s_c' = to_constraint (simplify s_c) in
          let v, asm =
            begin match s_c' with
            | None -> (r, if c = 0l then s_r2 else s_r1), pc.assumptions
            | Some s ->
              let x = Logicenv.next logic_env "__ternary" in
              Logicenv.add logic_env x r;
              let s_x = to_symbolic I32Type x in
              let t_eq  = I32Relop (I32Eq, s_x, s_r1) in
              let t_imp = I32Binop (I32Or, negate_relop s, t_eq) in
              let f_eq  = I32Relop (I32Eq, s_x, s_r2) in
              let f_imp = I32Binop (I32Or, s, f_eq) in
              let cond  = I32Binop (I32And, t_imp, f_imp) in
              (r, s_x), I32Relop (I32Ne, cond, Value (I32 0l)) :: pc.assumptions
            end
          in v :: vs', [], logic_env, {pc with assumptions = asm}, mem

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

        | SetPriority, _ :: _  :: _ :: vs' ->
          vs', [], logic_env, pc, mem

        | PopPriority, _ :: vs' ->
          vs', [], logic_env, pc, mem

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
        let c' = step {c with sym_code = code'} in
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
        let c' = step {
          sym_frame = frame';
          sym_code = code';
          logic_env = c.logic_env;
          path_cond = c.path_cond;
          sym_mem = c.sym_mem;
          sym_budget = c.sym_budget - 1
        }
        in vs, [SFrame (n, c'.sym_frame, c'.sym_code) @@ e.at], c'.logic_env, c'.path_cond, c'.sym_mem

      | SInvoke func, vs when c.sym_budget = 0 ->
        Exhaustion.error e.at "call stack exhausted"

      | SInvoke func, vs ->
        let symbolic_arg t =
          let x = Logicenv.next logic_env "arg" in
          let v = Logicenv.get logic_env x t false in
          (v, to_symbolic t x)
        in
        let FuncType (ins, out) = Func.type_of func in
        let n = List.length ins in
        let vs =
          if n > 0 && (List.length vs) = 0 then
            List.map (fun t -> symbolic_arg t) ins
          else vs
        in
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
    in
    { c with sym_code = vs', es' @ List.tl es; logic_env = logic_env';
             path_cond = pc'; sym_mem = mem' }

  let run
      (conf : sym_config ref)
      (inst : module_inst ref)
      (test_suite : string) =
    let test_cntr = count 1
    and ini_mem = Symmem2.to_list !inst.sym_memory
    and ini_code = !conf.sym_code
    and ini_glob = Global.contents !inst.globals
    and finish = ref false and err = ref None in
    let rec loop c =
      iterations := !iterations + 1; tree := head;
      let {logic_env = lenv; _} = try eval c step with
        | InstrLimit c'            -> finish := true; c'
        | AssumeFail (c', _)       -> iterations := !iterations - 1; c'
        | AssertFail (c', at)      -> err := Some ("Assertion Failure", at); c'
        | BugException (c', at, b) -> err := Some (string_of_bug b, at); c'
        | e -> raise e
      in
      let testcase = Logicenv.(to_json (to_list lenv)) in
      write_test_case test_suite testcase (Option.is_some !err) test_cntr;
      if Option.is_some !err then (
        incomplete := true;
        false, get_reason (Option.get !err), testcase
      ) else if !finish || X.is_empty to_explore then (
        true, "{}", "[]"
      ) else (
        let rec find_sat_pc pcs =
          if X.is_empty pcs then None
          else match timed_check_sat (Formula.to_formulas (X.pop pcs)) with
          | None -> find_sat_pc pcs
          | Some m -> Some m
        in
        match find_sat_pc to_explore with
        | None   -> true, "{}", "[]"
        | Some m -> loop (update_config m lenv c inst ini_mem ini_glob ini_code chk_tbl)
      )
    in
    loop_start := Sys.time ();
    let spec, reason, witness = loop !conf in
    let loop_time = (Sys.time ()) -. !loop_start in
    let n_lines = List.((length !inst.types) + (length !inst.tables) +
                        (length !inst.memories) + (length !inst.globals) +
                        (length !inst.exports) + 1) in
    let coverage = (Coverage.calculate_cov inst (n_lines + !lines_to_ignore)) *. 100.0 in
    write_report spec reason witness coverage loop_time;
    !conf.sym_code
end

(*
module CoverageSearch =
struct

  type tree =
    | Leaf
    | Node of tree ref * tree ref

  (* Execution tracing *)
  let head = ref Leaf
  let tree = ref head

  (* Priority of PCs to explore *)
  let to_explore = PQueue.create ()
  let pc_map = Hashtbl.create 128
  let p_stack = Stack.create ()

  (* Tracks malloc chunks (loc, size) *)
  let chk_tbl = Hashtbl.create 512

  let move_true (t : tree ref) : tree ref * bool =
    match !t with
    | Leaf ->
      let rt = ref Leaf and rf = ref Leaf in
      t := Node (rt, rf);
      rt, true
    | Node (rt, rf) -> rt, false

  let move_false (t : tree ref) : tree ref * bool =
    match !t with
    | Leaf ->
      let rt = ref Leaf and rf = ref Leaf in
      t := Node (rt, rf);
      rf, true
    | Node (rt, rf) -> rf, false

  let branch_on_cond bval c pc priority : unit =
    let c' = simplify c in
    if not (is_concrete c') then (
      let tree', to_branch = if bval then move_true !tree
                                     else move_false !tree in
      tree := tree';
      let pc' = pc.assumptions @ pc.branches in
      if to_branch then (
        PQueue.push priority to_explore;
        Hashtbl.add pc_map priority (add_constraint ~neg:bval c pc')
      )
    )

  (*  Symbolic step  *)
  let rec step (c : sym_config) : sym_config =
    step_cnt := !step_cnt + 1;
    let {
      sym_frame = frame;
      sym_code  = vs, es;
      logic_env = logic_env;
      path_cond = pc;
      sym_mem   = mem;
      _
    } = c in
    let e = List.hd es in
    Coverage.record_line (Source.get_line e.at);
    let vs', es', logic_env', pc', mem' =
      if (not (!Flags.inst_limit = -1)) && (!step_cnt >= !Flags.inst_limit) then (
        incomplete := true;
        vs, [Interrupt IntLimit @@ e.at], logic_env, pc, mem
      ) else (match e.it, vs with
      | SPlain e', vs ->
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
          let _, (p, _) = Stack.top p_stack in
          let _ = branch_on_cond false ex pc p in
          let pc' = { pc with branches = add_constraint ~neg:true ex pc.branches } in
          vs', [SPlain (Block (ts, es2)) @@ e.at], logic_env, pc', mem

        | If (ts, es1, es2), (I32 i, ex) :: vs' ->
          let _, (_, p) = Stack.top p_stack in
          let _ = branch_on_cond true ex pc p in
          let pc' = { pc with branches = add_constraint ex pc.branches } in
          vs', [SPlain (Block (ts, es1)) @@ e.at], logic_env, pc', mem

        | Br x, vs ->
          [], [SBreaking (x.it, vs) @@ e.at], logic_env, pc, mem

        | BrIf x, (I32 0l, ex) :: vs' ->
          let _, (p, _) = try Stack.top p_stack with Stack.Empty -> (0, (1, 1)) in
          let _ = branch_on_cond false ex pc p in
          let pc' = { pc with branches = add_constraint ~neg:true ex pc.branches } in
          vs', [], logic_env, pc', mem

        | BrIf x, (I32 i, ex) :: vs' ->
          let _, (_, p) = try Stack.top p_stack with Stack.Empty -> (0, (1, 1)) in
          let _ = branch_on_cond true ex pc p in
          let pc' = { pc with branches = add_constraint ex pc.branches } in
          vs', [SPlain (Br x) @@ e.at], logic_env, pc', mem

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
          let _ = branch_on_cond false ex pc 1 in
          let pc' = { pc with branches = add_constraint ~neg:true ex pc.branches } in
          v2 :: vs', [], logic_env, pc', mem

        | Select, (I32 i, ex) :: v2 :: v1 :: vs' ->
          let _ = branch_on_cond true ex pc 1 in
          let pc' = { pc with branches = add_constraint ex pc.branches } in
          v1 :: vs', [], logic_env, pc', mem

        | LocalGet x, vs ->
          !(local frame x) :: vs, [], logic_env, pc, mem

        | LocalSet x, (v, ex) :: vs' ->
          local frame x := (v, simplify ex);
          vs', [], logic_env, pc, mem

        | LocalTee x, (v, ex) :: vs' ->
          let ex' = simplify ex in
          local frame x := (v, ex');
          (v, ex') :: vs', [], logic_env, pc, mem

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
              let chunk_size =
                try Hashtbl.find chk_tbl low
                with Not_found -> raise (BugException (c, e.at, UAF)) in
              let high = Int64.(add (of_int32 low) (of_int32 chunk_size))
              and ptr_val = Int64.(add base (of_int32 offset)) in
              (* ptr_val \notin [low, high[ => overflow *)
              if ptr_val < (Int64.of_int32 low) || ptr_val >= high then
                raise (BugException (c, e.at, Overflow))
            end;
            let (v, e) =
              match sz with
              | None           -> Symmem2.load_value mem base offset ty
              | Some (sz, ext) -> Symmem2.load_packed sz ext mem base offset ty
            in
            (*print_endline ("after load: " ^ (Symvalue.to_string e));*)
            (v, e) :: vs', [], logic_env, pc, mem
          with
          | BugException (_, at, b) ->
            vs', [Interrupt (Bug b) @@ e.at], logic_env, pc, mem
          | exn ->
            vs', [STrapping (memory_error e.at exn) @@ e.at], logic_env, pc, mem
          end

        | Store {offset; sz; _}, (v, ex) :: (I32 i, sym_ptr) :: vs' ->
          let base = I64_convert.extend_i32_u i in
          let ptr = get_ptr (simplify sym_ptr) in
          begin try
            if Option.is_some ptr then begin
              let low = I32Value.of_value (Option.get ptr) in
              let chunk_size =
                try Hashtbl.find chk_tbl low
                with Not_found -> raise (BugException (c, e.at, UAF)) in
              let high = Int64.(add (of_int32 low) (of_int32 chunk_size))
              and ptr_val = Int64.(add base (of_int32 offset)) in
              if (Int64.of_int32 low) > ptr_val || ptr_val >= high then
                raise (BugException (c, e.at, Overflow))
            end;
            begin match sz with
            | None    -> Symmem2.store_value mem base offset (v, simplify ex)
            | Some sz -> Symmem2.store_packed sz mem base offset (v, simplify ex)
            end;
            vs', [], logic_env, pc, mem
          with
          | BugException (_, at, b) ->
            vs', [Interrupt (Bug b) @@ e.at], logic_env, pc, mem
          | exn ->
            vs', [STrapping (memory_error e.at exn) @@ e.at], logic_env, pc, mem
          end

        | MemorySize, vs ->
          let mem' = memory frame.sym_inst (0l @@ e.at) in
          let v = I32 (Memory.size mem') in
          (v, Value v) :: vs, [], logic_env, pc, mem

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
          vs', [Interrupt (AssFail pc.branches) @@ e.at], logic_env, pc, mem

        | SymAssert, (I32 i, ex) :: vs' -> (* != 0 on top of stack *)
          debug ">>> Assert reached. Checking satisfiability...";
          let es' =
            if is_concrete (simplify ex) then []
            else (
              let formulas = pc.assumptions @ (add_constraint ~neg:true ex pc.branches) in
              match timed_check_sat (Formula.to_formulas formulas) with
              | None   -> []
              | Some m ->
                let li32 = Logicenv.get_vars_by_type I32Type logic_env
                and li64 = Logicenv.get_vars_by_type I64Type logic_env
                and lf32 = Logicenv.get_vars_by_type F32Type logic_env
                and lf64 = Logicenv.get_vars_by_type F64Type logic_env in
                let binds = Z3Encoding2.lift_z3_model m li32 li64 lf32 lf64 in
                Logicenv.update logic_env binds;
                [Interrupt (AssFail pc.branches) @@ e.at]
            )
          in
          if es' = [] then debug "\n\n###### Assertion passed ######";
          vs', es', logic_env, pc, mem

        | SymAssume, (I32 0l, ex) :: vs' ->
          debug (">>> Assumed false {line> " ^ (Source.string_of_pos e.at.left) ^
            "}. Finishing...");
          if (not !Flags.smt_assume) || is_concrete (simplify ex) then (
            let _ = branch_on_cond false ex pc max_int in
            let pc' = { pc with branches = add_constraint ~neg:true ex pc.branches } in
            vs', [Interrupt (AsmFail pc'.branches) @@ e.at], logic_env, pc', mem
          ) else (
            let pc' = pc.assumptions @ (add_constraint ex pc.branches) in
            let formulas = Formula.to_formulas pc' in
            let vs'', es', pc'' = match timed_check_sat formulas with
              | None ->
                let _ = branch_on_cond false ex pc max_int in
                let pc_fls = { pc with branches = add_constraint ~neg:true ex pc.branches } in
                vs', [Interrupt (AsmFail pc') @@ e.at], pc_fls
              | Some m ->
                (* Record path *)
                if not (is_concrete (simplify ex)) then (
                  let tree', _ = move_true !tree in
                  tree := tree'
                );
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
                List.map f vs', [], {pc with branches = pc'}
            in vs'', es', logic_env, pc'', mem)

        | SymAssume, (I32 i, ex) :: vs' ->
          debug ">>> Assume passed. Continuing execution...";
          if not (is_concrete (simplify ex)) then (
            let tree', _ = move_true !tree in
            tree := tree'
          );
          let pc' = { pc with branches = add_constraint ex pc.branches } in
          vs', [], logic_env, pc', mem

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
            Hashtbl.add chk_tbl b a;
            (I32 b, Ptr (I32 b)) :: vs', [], logic_env, pc, mem

        | Free, (I32 i, _) :: vs' ->
          let es' =
            if not (Hashtbl.mem chk_tbl i) then (
              [Interrupt (Bug InvalidFree) @@ e.at]
            ) else (
              Hashtbl.remove chk_tbl i;
              []
            )
          in vs', es', logic_env, pc, mem

        (* Deprecated *)
        | SymInt32 x, vs' ->
          let v =
            try Logicenv.find logic_env x with
            | Not_found ->
              let v' = I32 (I32.rand 1000) in
              Logicenv.add logic_env x v';
              v'
          in (v, Symvalue.Symbolic (SymInt32, x)) :: vs', [], logic_env, pc, mem

        (* Deprecated *)
        | SymInt64 x, vs' ->
          let v =
            try Logicenv.find logic_env x with
            | Not_found ->
              let v' = I64 (I64.rand 1000) in
              Logicenv.add logic_env x v';
              v'
          in (v, Symvalue.Symbolic (SymInt64, x)) :: vs', [], logic_env, pc, mem

        (* Deprecated *)
        | SymFloat32 x, vs' ->
          let v =
            try Logicenv.find logic_env x with
            | Not_found ->
              let v' = F32 (F32.rand 1000.0) in
              Logicenv.add logic_env x v';
              v'
          in (v, Symvalue.Symbolic (SymFloat32, x)) :: vs', [], logic_env, pc, mem

        (* Deprecated *)
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

        | TernaryOp, (I32 r2, s_r2) :: (I32 r1, s_r1) :: (I32 c, s_c) :: vs' ->
          let r = I32 (if c = 0l then r2 else r1) in
          let s_c' = to_constraint (simplify s_c) in
          let v, asm =
            begin match s_c' with
            | None -> (r, if c = 0l then s_r2 else s_r1), pc.assumptions
            | Some s ->
              let x = Logicenv.next logic_env "__ternary" in
              Logicenv.add logic_env x r;
              let s_x = to_symbolic I32Type x in
              let t_eq  = I32Relop (I32Eq, s_x, s_r1) in
              let t_imp = I32Binop (I32Or, negate_relop s, t_eq) in
              let f_eq  = I32Relop (I32Eq, s_x, s_r2) in
              let f_imp = I32Binop (I32Or, s, f_eq) in
              let cond  = I32Binop (I32And, t_imp, f_imp) in
              (r, s_x), I32Relop (I32Ne, cond, Value (I32 0l)) :: pc.assumptions
            end
          in v :: vs', [], logic_env, {pc with assumptions = asm}, mem

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
          let eq = I32 1l and ne = I32 0l in
          let v =
            match ex1, ex2 with
            | Symbolic (SymInt32, x), Symbolic (SymInt32, y) ->
              let c = if x = y then eq else ne in
              c, Symvalue.I32Relop (I32Eq, ex1, ex2)
            | _, _ ->
              eval_relop (v1, ex1) (v2, ex2) (Values.I32 Ast.I32Op.Eq)
          in
          v :: vs', [], logic_env, pc, mem

        | IsSymbolic, (I32 n, _) :: (I32 i, _) :: vs' ->
          let base = I64_convert.extend_i32_u i in
          let (_, v) = Symmem2.load_bytes mem base (Int32.to_int n) in
          (* TODO: Better symbolic matcher (deal with extract of symbolics) *)
          let ans = match v with
            | Symbolic _ -> I32 1l
            | _ -> I32 0l
          in
          (*Printf.printf "%d %d\n" (Int32.to_int i) (Int64.to_int addr);*)
          (ans, Value ans) :: vs', [], logic_env, pc, mem

        | SetPriority, (I32 f, _) :: (I32 t, _)  :: (I32 id, _) :: vs' ->
          let id', t', f' = Int32.to_int id, Int32.to_int t, Int32.to_int f in
          let _ = Stack.push (id', (t', f')) p_stack in
          vs', [], logic_env, pc, mem

        | PopPriority, (I32 id, _) :: vs' ->
          let id', _ = Stack.pop p_stack in
          if (Int32.to_int id) <> id' then
            print_endline ("found misaligned priority block");
          vs', [], logic_env, pc, mem

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
        let c' = step {c with sym_code = code'} in
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
        let c' = step {
          sym_frame = frame';
          sym_code = code';
          logic_env = c.logic_env;
          path_cond = c.path_cond;
          sym_mem = c.sym_mem;
          sym_budget = c.sym_budget - 1
        }
        in vs, [SFrame (n, c'.sym_frame, c'.sym_code) @@ e.at], c'.logic_env, c'.path_cond, c'.sym_mem

      | SInvoke func, vs when c.sym_budget = 0 ->
        Exhaustion.error e.at "call stack exhausted"

      | SInvoke func, vs ->
        let symbolic_arg t =
          let x = Logicenv.next logic_env "arg" in
          let v = Logicenv.get logic_env x t false in
          (v, to_symbolic t x)
        in
        let FuncType (ins, out) = Func.type_of func in
        let n = List.length ins in
        let vs =
          if n > 0 && (List.length vs) = 0 then
            List.map (fun t -> symbolic_arg t) ins
          else vs
        in
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
    in
    { c with sym_code = vs', es' @ List.tl es; logic_env = logic_env';
             path_cond = pc'; sym_mem = mem' }

  let run
      (conf : sym_config ref)
      (inst : module_inst ref)
      (test_suite : string) =
    let test_cntr = count 1
    and ini_mem = Symmem2.to_list !inst.sym_memory
    and ini_code = !conf.sym_code
    and ini_glob = Global.contents !inst.globals
    and finish = ref false and err = ref None in
    let rec loop c =
      iterations := !iterations + 1; tree := head;
      let {logic_env = lenv; _} = try eval c step with
        | InstrLimit c'            -> finish := true; c'
        | AssumeFail (c', _)       -> iterations := !iterations - 1; c'
        | AssertFail (c', at)      -> err := Some ("Assertion Failure", at); c'
        | BugException (c', at, b) -> err := Some (string_of_bug b, at); c'
        | e -> raise e
      in
      let testcase = Logicenv.(to_json (to_list lenv)) in
      write_test_case test_suite testcase (Option.is_some !err) test_cntr;
      if Option.is_some !err then (
        incomplete := true;
        false, get_reason (Option.get !err), testcase
      ) else if !finish || PQueue.is_empty to_explore then (
        true, "{}", "[]"
      ) else (
        let rec find_sat_pc pcs =
          if PQueue.is_empty pcs then None
          else (
            let priority = PQueue.pop pcs in
            let pc = Hashtbl.find pc_map priority in
            Hashtbl.remove pc_map priority;
            match timed_check_sat (Formula.to_formulas pc) with
            | None -> find_sat_pc pcs
            | Some m -> Some m
          )
        in
        match find_sat_pc to_explore with
        | None   -> true, "{}", "[]"
        | Some m -> loop (update_config m lenv c inst ini_mem ini_glob ini_code chk_tbl)
      )
    in
    loop_start := Sys.time ();
    let spec, reason, witness = loop !conf in
    let loop_time = (Sys.time ()) -. !loop_start in
    let n_lines = List.((length !inst.types) + (length !inst.tables) +
                        (length !inst.memories) + (length !inst.globals) +
                        (length !inst.exports) + 1) in
    let coverage = (Coverage.calculate_cov inst (n_lines + !lines_to_ignore)) *. 100.0 in
    write_report spec reason witness coverage loop_time;
    !conf.sym_code
end
*)

module Rnd = RandomSearch
(* module Cov = CoverageSearch *)
module DFS = GuidedSearch(Stack)
module BFS = GuidedSearch(Queue)

let sym_invoke' (func : func_inst) (vs : sym_value list) : sym_value list =
  (* Prepare workspace *)
  let test_suite = Filename.concat !Flags.output "test_suite" in
  Io.safe_mkdir test_suite;
  (* Prepare inital configuration *)
  let at = match func with Func.AstFunc (_, _, f) -> f.at | _ -> no_region in
  let inst = try Option.get (Func.get_inst func)
             with Invalid_argument s -> Crash.error at ("sym_invoke: " ^ s) in
  let c = ref (sym_config empty_module_inst (List.rev vs) [SInvoke func @@ at]
    !inst.sym_memory) in
  (* Set analysis time limit *)
  set_timeout !Flags.timeout;
  (* Dispatch *)
  let p = parse_policy !Flags.policy in
  let f = match p with
    | None -> Crash.error at "wrong search policy provided."
    | Some Random   -> Rnd.run
    | Some Depth    -> DFS.run
    | Some Breadth  -> BFS.run
    (* | Some Coverage -> Cov.run *)
  in
  let (vs, _) = f c inst test_suite in
  try List.rev vs with Stack_overflow ->
    Exhaustion.error at "call stack exhausted"

let eval_const (inst : module_inst) (const : const) : value =
  let sym_mem = inst.sym_memory in
  let c = sym_config inst [] (List.map plain const.it) sym_mem in
  let res = eval c Rnd.step in
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
