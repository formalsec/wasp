type bug =
  | Overflow
  | UAF
  | InvalidFree

type interruption =
  | IntLimit
  | AsmFail of Symvalue.path_conditions
  | AssFail of string
  | Bug of bug * string

(*  Symbolic Frame  *)
type sym_frame =
{
  sym_inst : Instance.module_inst;
  sym_locals : Symvalue.sym_expr ref list; (*  Locals can be symbolic  *)
}

(*  Symbolic code  *)
type sym_code = Symvalue.sym_expr list * sym_admin_instr list
and sym_admin_instr = sym_admin_instr' Source.phrase
and instr = Ast.instr' Source.phrase
and sym_admin_instr' =
  | SPlain of Ast.instr'
  | SInvoke of Instance.func_inst
  | STrapping of string
  | SReturning of Symvalue.sym_expr list
  | SBreaking of int32 * Symvalue.sym_expr list
  | SLabel of int * instr list * sym_code
  | SFrame of int * sym_frame * sym_code
  (**
    * Wasp's administrative instructions to halt
    * small-step semantic intepretation
    *)
  | Interrupt of interruption

module type EncodingStrategy =
  sig
    type sym_config

    val clone : sym_config -> sym_config

    val time_solver : float ref

    val sym_config :
      Instance.module_inst ->
      Symvalue.sym_expr list ->
      sym_admin_instr list ->
      Heap.t ->
      Static_globals.t -> sym_config

    val step : sym_config -> ((sym_config list * Symvalue.path_conditions list), string * string) result
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

module TreeStrategy (L : WorkList) (ES : EncodingStrategy) =
struct
  let eval (c : ES.sym_config) : (Symvalue.path_conditions list, string * string) result =
    let w = L.create () in
    L.push c w;

    let err = ref None in
    let outs = ref [] in
    while Option.is_none !err && not ((L.is_empty w)) do
      let c = L.pop w in
      match (ES.step c) with
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

module BFS_L (ES : EncodingStrategy) =
struct
  let max_configs = 32

  let eval (c : ES.sym_config) : (Symvalue.path_conditions list, string * string) result =
    let w = Queue.create () in
    Queue.push c w;

    let err = ref None in
    let outs = ref [] in
    while Option.is_none !err && not ((Queue.is_empty w)) do
      let l = Queue.length w in
      let c = Queue.pop w in
      match (ES.step c) with
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

module Half_BFS (ES : EncodingStrategy) =
struct
  let max_configs = 512

  let eval (c : ES.sym_config) : (Symvalue.path_conditions list, string * string) result =
    let w = Queue.create () in
    Queue.push c w;

    let err = ref None in
    let outs = ref [] in
    while Option.is_none !err && not ((Queue.is_empty w)) do
      let c = Queue.pop w in
      match (ES.step c) with
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

module ProgressBFS (ES : EncodingStrategy) =
struct
  let eval (c : ES.sym_config) : (Symvalue.path_conditions list, string * string) result =
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
        match (ES.step c) with
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

module RS (ES : EncodingStrategy) =
struct
  let sym_config = ES.sym_config

  let eval (c : ES.sym_config) : (Symvalue.path_conditions list, string * string) result =
    let open Batteries in

    let swap (v : ES.sym_config BatDynArray.t) (x : int) (y : int) =
      let tmp = BatDynArray.get v x in
      BatDynArray.set v x (BatDynArray.get v y);
      BatDynArray.set v y tmp;
    in

    let w = BatDynArray.create () in
    BatDynArray.add w c;

    let err = ref None in
    let outs = ref [] in
    while Option.is_none !err && not ((BatDynArray.empty w)) do
      if BatDynArray.length w > 1 then begin
        let idx = Random.int (BatDynArray.length w) in
        swap w idx (BatDynArray.length w - 1);
      end;
      let c = BatDynArray.last w in
      BatDynArray.delete_last w;

      match (ES.step c) with
      | Result.Ok (cs', outs') -> begin
        BatDynArray.append (BatDynArray.of_list cs') w;

        outs := !outs @ outs';
      end
      | Result.Error step_err -> begin
        err := Some step_err;
      end;
    done;

    match !err with
    | Some step_err -> Result.error step_err
    | None -> Result.ok !outs
end

module Helper (ES : EncodingStrategy) =
struct
  module DFS_ES = DFS(ES)
  module BFS_ES = BFS(ES)
  module BFS_L_ES = BFS_L(ES)
  module Half_BFS_ES = Half_BFS(ES)
  module RS_ES = RS(ES)
  let helper
      (inst : Instance.module_inst)
      (vs : Symvalue.sym_expr list)
      (es : sym_admin_instr list)
      (sym_m : Heap.t)
      (globs : Static_globals.t)
      : bool * string * string * float * float * int =
    let c = ES.sym_config inst vs es sym_m globs in

    let eval = match !Flags.policy with
    | "depth" -> DFS_ES.eval
    | "breadth" -> BFS_ES.eval
    | "breadth-l" -> BFS_L_ES.eval
    | "half-breadth" -> Half_BFS_ES.eval
    | "random" -> RS_ES.eval
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

    spec, reason, witness, loop_time, !ES.time_solver, paths
end
