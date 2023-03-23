type bug =
  | Overflow
  | UAF
  | InvalidFree

type interruption =
  | IntLimit
  | AsmFail of Expression.path_conditions
  | AssFail of string
  | Bug of bug * string

(*  Symbolic Frame  *)
type sym_frame =
{
  sym_inst : Interpreter.Instance.module_inst;
  sym_locals : Expression.t ref list; (*  Locals can be symbolic  *)
}

(*  Symbolic code  *)
type sym_code = Expression.t list * sym_admin_instr list
and sym_admin_instr = sym_admin_instr' Interpreter.Source.phrase
and instr = Interpreter.Ast.instr' Interpreter.Source.phrase
and sym_admin_instr' =
  | SPlain of Interpreter.Ast.instr'
  | SInvoke of Interpreter.Instance.func_inst
  | STrapping of string
  | SReturning of Expression.t list
  | SBreaking of int32 * Expression.t list
  | SLabel of int * instr list * sym_code
  | SFrame of int * sym_frame * sym_code
  (**
    * Wasp's administrative instructions to halt
    * small-step semantic intepretation
    *)
  | Interrupt of interruption

module type Interpreter =
  sig
    type sym_config

    val clone : sym_config -> sym_config * sym_config

    val time_solver : float ref

    val sym_config :
      Interpreter.Instance.module_inst ->
      Expression.t list ->
      sym_admin_instr list ->
      Concolic.Heap.t ->
      Globals.t -> sym_config

    val step : sym_config -> ((sym_config list * Expression.path_conditions list), string * string) result
  end

module type WorkList =
sig
  type 'a t
  exception Empty
  val create : unit -> 'a t
  val push : 'a -> 'a t -> unit
  val pop : 'a t -> 'a
  val add_seq : 'a t -> 'a Seq.t -> unit
  val is_empty : 'a t -> bool
  val length : 'a t -> int
end

module TreeStrategy (L : WorkList) (I : Interpreter) =
struct
  let eval (c : I.sym_config) : (Expression.path_conditions list, string * string) result =
    let w = L.create () in
    L.push c w;

    let err = ref None in
    let outs = ref [] in
    while Option.is_none !err && not ((L.is_empty w)) do
      let c = L.pop w in
      match (I.step c) with
      | Result.Ok (cs', outs') -> begin
        L.add_seq w (List.to_seq cs');
        outs := !outs @ outs';
      end
      | Result.Error step_err -> begin
        err := Some step_err;
      end
    done;

    match !err with
    | Some step_err -> Result.error step_err
    | None -> Result.ok !outs
end

module DFS = TreeStrategy(Stack)
module BFS = TreeStrategy(Queue)
module RS = TreeStrategy(Common.RandArray)

module BFS_L (I : Interpreter) =
struct
  let max_configs = 32

  let eval (c : I.sym_config) : (Expression.path_conditions list, string * string) result =
    let w = Queue.create () in
    Queue.push c w;

    let err = ref None in
    let outs = ref [] in
    while Option.is_none !err && not ((Queue.is_empty w)) do
      let l = Queue.length w in
      let c = Queue.pop w in
      match (I.step c) with
      | Result.Ok (cs', outs') -> begin
        if l + List.length cs' <= max_configs then
          Queue.add_seq w (List.to_seq cs')
        else
          Queue.push c w;
        outs := !outs @ outs';
      end
      | Result.Error step_err -> begin
        err := Some step_err;
      end
    done;

    match !err with
    | Some step_err -> Result.error step_err
    | None -> Result.ok !outs
end

module Half_BFS (I : Interpreter) =
struct
  let max_configs = 512

  let eval (c : I.sym_config) : (Expression.path_conditions list, string * string) result =
    let w = Queue.create () in
    Queue.push c w;

    let err = ref None in
    let outs = ref [] in
    while Option.is_none !err && not ((Queue.is_empty w)) do
      let c = Queue.pop w in
      match (I.step c) with
      | Result.Ok (cs', outs') -> begin
        Queue.add_seq w (List.to_seq cs');
        outs := !outs @ outs';
      end
      | Result.Error step_err -> begin
        err := Some step_err;
      end;
      let l = Queue.length w in
      if l >= max_configs - 2 then
        let filtered = Queue.of_seq (Seq.filter_map (fun c -> if Random.bool () then Some c else None) (Queue.to_seq w)) in
        Queue.clear w;
        Queue.transfer filtered w;
    done;

    match !err with
    | Some step_err -> Result.error step_err
    | None -> Result.ok !outs
end

module ProgressBFS (I : Interpreter) =
struct
  let eval (c : I.sym_config) : (Expression.path_conditions list, string * string) result =
    let max_configs = ref 2 in
    let hot = Queue.create () in
    Queue.push c hot;
    let cold = Queue.create () in

    let err = ref None in
    let outs = ref [] in

    while Option.is_none !err && not (Queue.is_empty hot && Queue.is_empty cold) do
      while Option.is_none !err && not ((Queue.is_empty hot)) do
        let l = Queue.length hot in
        let c = Queue.pop hot in
        match (I.step c) with
        | Result.Ok (cs', outs') -> begin
          if l + List.length cs' <= !max_configs then
            Queue.add_seq hot (List.to_seq cs')
          else
            Queue.add_seq cold (List.to_seq cs');
          outs := !outs @ outs';
        end
        | Result.Error step_err -> begin
          err := Some step_err
        end;
      done;
      Queue.transfer cold hot;
      (* only increase max size if we have a lot of splits *)
      if Queue.length hot >= !max_configs * 3 / 4 then
        max_configs := !max_configs * 2;
    done;

    match !err with
    | Some step_err -> Result.error step_err
    | None -> Result.ok !outs
end

module Helper (I : Interpreter) =
struct
  module DFS_I = DFS(I)
  module BFS_I = BFS(I)
  module BFS_L_I = BFS_L(I)
  module Half_BFS_I = Half_BFS(I)
  module RS_I = RS(I)
  let helper
      (inst : Interpreter.Instance.module_inst)
      (vs : Expression.t list)
      (es : sym_admin_instr list)
      (sym_m : Concolic.Heap.t)
      (globs : Globals.t)
      : bool * string * string * float * float * int =
    let c = I.sym_config inst vs es sym_m globs in

    let eval = match !Interpreter.Flags.policy with
    | "depth" -> DFS_I.eval
    | "breadth" -> BFS_I.eval
    | "breadth-l" -> BFS_L_I.eval
    | "half-breadth" -> Half_BFS_I.eval
    | "random" -> RS_I.eval
    | _ -> failwith "unreachable"
    in

    let loop_start = Sys.time () in
    let (spec, reason, witness, paths) = match (eval c) with
    | Result.Ok pcs -> (
      (true, "{}", "[]", List.length pcs)
    )
    | Result.Error (reason, witness) -> (
      (false, reason, witness, 1)
    )
    in

    let loop_time = (Sys.time()) -. loop_start in

    spec, reason, witness, loop_time, !I.time_solver, paths
end
