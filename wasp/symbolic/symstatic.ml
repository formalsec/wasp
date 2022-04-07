open Values
open Symvalue
open Types
open Instance
open Ast
open Source
(* open Evaluations *)
(* open Si32 *)

(* Errors *)

module Link = Error.Make ()
module Trap = Error.Make ()
module Crash = Error.Make ()
module Exhaustion = Error.Make ()

exception Link = Link.Error
exception Trap = Trap.Error
exception Crash = Crash.Error (* failure that cannot happen in valid code *)
exception Exhaustion = Exhaustion.Error

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
  sym_locals : sym_expr ref list; (*  Locals can be symbolic  *)
}

let clone(frame: sym_frame): sym_frame =
  let sym_inst = clone(frame.sym_inst) in
  let sym_locals = frame.sym_locals in
  {
    sym_inst = sym_inst;
    sym_locals = sym_locals;
  }

(*  Symbolic code  *)
type sym_code = sym_expr stack * sym_admin_instr list

and sym_admin_instr = sym_admin_instr' phrase
and sym_admin_instr' =
  | SPlain of instr'
  | SInvoke of func_inst
  | STrapping of string
  | SReturning of sym_expr stack
  | SBreaking of int32 * sym_expr stack
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
  path_cond  : path_conditions;
  sym_mem    : Symmem2.t;
  sym_budget : int;  (* to model stack overflow *)
  var_map    : Varmap.t;
}

let clone(c: sym_config): sym_config =
  let sym_frame = clone(c.sym_frame) in
  let sym_code = c.sym_code in
  let path_cond = c.path_cond in
  let sym_mem = (Symmem2.clone c.sym_mem) in
  let sym_budget = c.sym_budget in
  let var_map = Hashtbl.copy(c.var_map) in
  {
    sym_frame = sym_frame;
    sym_code = sym_code;
    path_cond = path_cond;
    sym_mem = sym_mem;
    sym_budget = sym_budget;
    var_map = var_map;
  }

(* Symbolic frame and configuration  *)
let sym_frame sym_inst sym_locals = {sym_inst; sym_locals}
let sym_config inst vs es sym_m = {
  sym_frame  = sym_frame inst [];
  sym_code   = vs, es;
  path_cond  = [];
  sym_mem    = sym_m;
  sym_budget = 100000; (* models default recursion limit in a system *)
  var_map = Hashtbl.create 100;
}

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

let rec step (c : sym_config) : ((sym_config list * sym_config list), string) result =
  let {
    sym_frame = frame;
    sym_code = vs, es;
    path_cond = pc;
    sym_mem = mem;
    var_map = var_map;
    _} = c in
  match es with
  | [] -> Result.ok ([], [c])
  | e :: t ->
  (match e.it, vs with
    | SPlain e', vs ->
      print_endline((instr_str e'));
      (match e', vs with
      | Nop, vs ->
        Result.ok ([ { c with sym_code = vs, List.tl es } ], [])

      | Drop, v :: vs' ->
        Result.ok ([ { c with sym_code = vs', List.tl es } ], [])

      | Block (ts, es'), vs ->
        let es0 = SLabel (List.length ts, [], ([], List.map plain es')) @@ e.at in
        Result.ok ([ { c with sym_code = vs, es0 :: (List.tl es) } ], [])

      | If (ts, es1, es2), (ex) :: vs' ->
        (match ex with
        | Value (I32 0l) ->
          (* if it is 0 *)
          Result.ok ([ { c with sym_code = vs', [SPlain (Block (ts, es2)) @@ e.at]} ], [])
        | Value (I32 _) ->
          (* if it is not 0 *)
          Result.ok ([ { c with sym_code = vs', [SPlain (Block (ts, es1)) @@ e.at]} ], [])
        | _ -> (
          let c_clone = clone c in
          let pc_false = add_constraint ex pc true in
          let pc_true = add_constraint ex pc false in
          (* TODO: check if ex != 0 is sat and if so include that config *)
          let c_true = { c with sym_code = vs', [SPlain (Block (ts, es1)) @@ e.at] ; path_cond = pc_true } in
          (* TODO: check if ex == 0 is sat and if so include that config *)
          let c_false = { c_clone with sym_code = vs', [SPlain (Block (ts, es2)) @@ e.at] ; path_cond = pc_false } in
          Result.ok ([ c_true; c_false ], [])
          )
        )

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
        let v' = Global.load (global frame.sym_inst x) in
        let es' = List.tl es in
        Result.ok ([ { c with sym_code = (Value v') :: vs, es' } ], [])

      | Const v, vs ->
        let es' = List.tl es in
        Result.ok ([ { c with sym_code = (Value v.it) :: vs, es' } ], [])

      | Dup, v :: vs' ->
        let vs'' = v :: v :: vs' in
        let es' = List.tl es in
        Result.ok ([ { c with sym_code = (vs'', es') } ], [])

      | SymAssert, (Value (I32 0l)) :: vs' ->
        (* TODO: finish this? *)
        (* debug ">>> Assert FAILED! Stopping..."; *)
        failwith "Reached SymAssert with 0"

      | SymAssert, (Value (I32 _)) :: vs' ->
        (* passed *)
        Result.ok ([ { c with sym_code = vs', List.tl es } ], [])

      | SymAssert, v :: vs' ->
        (let opt_c =
        (match simplify v with
        | Value (I32 v) when not (v = 0l) -> None
        | Ptr   (I32 v) when not (v = 0l) -> None
        | ex' ->
          let c = Option.map negate_relop (to_constraint ex') in
          let pc' = Option.map_default (fun a -> a :: pc) pc c in
          let assertion = Formula.to_formula pc' in
          let model = Z3Encoding2.check_sat_core assertion in
          match model with
          | None   -> None
          | Some m ->
            let li32 = Varmap.get_vars_by_type I32Type var_map
            and li64 = Varmap.get_vars_by_type I64Type var_map
            and lf32 = Varmap.get_vars_by_type F32Type var_map
            and lf64 = Varmap.get_vars_by_type F64Type var_map in
            let binds = Z3Encoding2.lift_z3_model m li32 li64 lf32 lf64 in
            Some Logicenv.(to_json binds)
        )
        in
        match opt_c with
        | Some c -> Result.error c
        | None -> Result.ok ([ { c with sym_code = (vs', List.tl es) } ], [])
        )

      | SymAssume, ex :: vs' ->
        (match simplify ex with
        | Ptr   (I32 0l)
        | Value (I32 0l) ->
          (* if it is 0 *)
          (* TODO: what to do? *)
          Result.ok ([], [])
        | Ptr   (I32 _)
        | Value (I32 _) ->
          (* if it is not 0 *)
          Result.ok ([ { c with sym_code = vs, List.tl es } ], [])
        | ex' -> (
          let pc_true = add_constraint ex' pc false in
          let assertion = Formula.to_formula pc_true in
          let model = Z3Encoding2.check_sat_core assertion in
          match model with
          | None   ->
            Result.ok ([], [])
          | Some _ ->
            let c_true = { c with sym_code = vs', List.tl es ; path_cond = pc_true } in
            print_endline "added";
            Result.ok ([ c_true ], []);
          )
        )

      | Symbolic (ty, b), (Value (I32 i)) :: vs' ->
        let base = I64_convert.extend_i32_u i in
        let x = Symmem2.load_string mem base in
        let v = to_symbolic ty x in
        let es' = List.tl es in
        Hashtbl.replace var_map x ty;
        Result.ok ([ { c with sym_code = (v :: vs', es') } ], [])

      | PrintStack, vs ->
        let vs' = List.map (fun v -> (Symvalue.pp_to_string v)) vs in
        print_endline ("Stack:" ^ "\n" ^ (String.concat "\n" vs'));
        let es' = List.tl es in
        Result.ok ([ { c with sym_code = vs, es' } ], [])

      (* TODO: PrintMem *)
      (* TODO: Assert *)

      | _ ->
        failwith ("Not implemented" ^ instr_str e')
      )

  | SLabel (n, es0, (vs', [])), vs ->
    Result.ok ([ { c with sym_code = vs' @ vs, List.tl es } ], [])

  | SLabel (n, es0, (vs', {it = Interrupt i; at} :: es')), vs ->
    let es' = (Interrupt i @@ at) :: [SLabel (n, es0, (vs', es')) @@ e.at] in
    Result.ok ([ { c with sym_code = vs, es' @ (List.tl es) } ], [])

  | SLabel (n, es0, (vs', {it = STrapping msg; at} :: es')), vs ->
    (* TODO *)
    Result.ok ([], [])

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
      (cs' @ outs'), [])) (step {c with sym_code = code'})

  | SFrame (n, frame', (vs', [])), vs ->
    Result.ok ([ { c with sym_code = vs' @ vs, List.tl es } ], [])

  | SFrame (n, frame', (vs', {it = Interrupt i; at} :: es')), vs ->
    let es' = (Interrupt i @@ at) :: [SFrame (n, frame', (vs', es')) @@ e.at] in
    Result.ok ([ { c with sym_code = vs, es' @ (List.tl es) } ], [])

  | SFrame (n, frame', (vs', {it = STrapping msg; at} :: es')), vs ->
    (* TODO *)
    Result.ok ([], [])

  | SFrame (n, frame', (vs', {it = SReturning vs0; at} :: es')), vs ->
    let vs'' = take n vs0 e.at @ vs in
    Result.ok ([ { c with sym_code = vs'', List.tl es } ], [])

  | SFrame (n, frame', code'), vs ->
    (* FIXME: path conditions *)
    Result.map (fun (cs', outs') ->
      (List.map (fun c ->
        let es0 = SFrame (n, c.sym_frame, c.sym_code) @@ e.at in
        { c with sym_code = vs, es0 :: (List.tl es) }
      ) (cs' @ outs'), [])
    ) (step {
      sym_frame = frame';
      sym_code = code';
      path_cond = c.path_cond;
      sym_mem = c.sym_mem;
      sym_budget = c.sym_budget - 1;
      var_map = c.var_map;
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

let rec eval (cs : sym_config list) (outs : sym_config list) :
    ((sym_config list * sym_config list), string) result =
  match cs with
  | [] -> Result.ok ([], outs)

  | c :: t ->
      match (step c) with
      | Result.Ok (cs', outs') -> eval (cs' @ t) (outs' @ outs)
      | err -> err

let invoke (func : func_inst) (vs : sym_expr list) : unit =
  let at = match func with Func.AstFunc (_, _, f) -> f.at | _ -> no_region in
  let inst = try Option.get (Func.get_inst func) with Invalid_argument s ->
    Crash.error at ("sym_invoke: " ^ s) in
  let c = sym_config empty_module_inst (List.rev vs) [SInvoke func @@ at]
    !inst.sym_memory in
  match (eval [c] []) with
  | Result.Ok _ -> ()
  | Result.Error str -> (
    print_endline str
  )

