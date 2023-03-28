open Common
open Encoding

type bug = Overflow | UAF | InvalidFree
type interruption = IntLimit | AssFail of string | Bug of bug * string

(*  Symbolic Frame  *)
type sym_frame = {
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

module type Interpreter = sig
  type sym_config
  type step_res = End of Encoding.Formula.t | Continuation of sym_config list

  val clone : sym_config -> sym_config * sym_config

  val sym_config :
    Interpreter.Instance.module_inst ->
    Expression.t list ->
    sym_admin_instr list ->
    Concolic.Heap.t ->
    Globals.t ->
    sym_config

  val step : sym_config -> (step_res, string * Interpreter.Source.region) result

  val concolic_invoke :
    sym_config -> (string * Interpreter.Source.region) option

  val p_invoke :
    sym_config ->
    (Encoding.Formula.t, string * Interpreter.Source.region) result

  val p_finished : sym_config -> Encoding.Formula.t -> sym_config option
end

module TreeStrategy (L : Wlist.WorkList) (I : Interpreter) = struct
  let eval (c : I.sym_config) :
      Encoding.Formula.t list * (string * Interpreter.Source.region) option =
    let w = L.create () in
    L.push c w;

    let err = ref None in
    let outs = ref [] in
    while Option.is_none !err && not (L.is_empty w) do
      let c = L.pop w in
      match I.step c with
      | Result.Ok step_res -> (
          match step_res with
          | I.Continuation cs' -> L.add_seq w (List.to_seq cs')
          | I.End e -> outs := e :: !outs)
      | Result.Error step_err -> err := Some step_err
    done;

    (!outs, !err)
end

module DFS = TreeStrategy (Stack)
module BFS = TreeStrategy (Queue)
module RS = TreeStrategy (RandArray)

module BFS_L (I : Interpreter) = struct
  let max_configs = 32

  let eval (c : I.sym_config) :
      Encoding.Formula.t list * (string * Interpreter.Source.region) option =
    let w = Queue.create () in
    Queue.push c w;

    let err = ref None in
    let outs = ref [] in
    while Option.is_none !err && not (Queue.is_empty w) do
      let l = Queue.length w in
      let c = Queue.pop w in
      match I.step c with
      | Result.Ok step_res -> (
          match step_res with
          | I.Continuation cs' ->
              if l + List.length cs' <= max_configs then
                Queue.add_seq w (List.to_seq cs')
              else Queue.push c w
          | I.End e -> outs := e :: !outs)
      | Result.Error step_err -> err := Some step_err
    done;

    (!outs, !err)
end

module Half_BFS (I : Interpreter) = struct
  let max_configs = 512

  let eval (c : I.sym_config) :
      Encoding.Formula.t list * (string * Interpreter.Source.region) option =
    let w = Queue.create () in
    Queue.push c w;

    let err = ref None in
    let outs = ref [] in
    while Option.is_none !err && not (Queue.is_empty w) do
      let c = Queue.pop w in
      match I.step c with
      | Result.Ok step_res -> (
          match step_res with
          | I.Continuation cs' -> Queue.add_seq w (List.to_seq cs')
          | I.End e -> outs := e :: !outs)
      | Result.Error step_err ->
          err := Some step_err;
          let l = Queue.length w in
          if l >= max_configs - 2 then (
            let filtered =
              Queue.of_seq
                (Seq.filter_map
                   (fun c -> if Random.bool () then Some c else None)
                   (Queue.to_seq w))
            in
            Queue.clear w;
            Queue.transfer filtered w)
    done;

    (!outs, !err)
end

module ProgressBFS (I : Interpreter) = struct
  let eval (c : I.sym_config) :
      Encoding.Formula.t list * (string * Interpreter.Source.region) option =
    let max_configs = ref 2 in
    let hot = Queue.create () in
    Queue.push c hot;
    let cold = Queue.create () in

    let err = ref None in
    let outs = ref [] in

    while
      Option.is_none !err && not (Queue.is_empty hot && Queue.is_empty cold)
    do
      while Option.is_none !err && not (Queue.is_empty hot) do
        let l = Queue.length hot in
        let c = Queue.pop hot in
        match I.step c with
        | Result.Ok step_res -> (
            match step_res with
            | I.Continuation cs' ->
                if l + List.length cs' <= !max_configs then
                  Queue.add_seq hot (List.to_seq cs')
                else Queue.add_seq cold (List.to_seq cs')
            | I.End e -> outs := e :: !outs)
        | Result.Error step_err -> err := Some step_err
      done;
      Queue.transfer cold hot;
      (* only increase max size if we have a lot of splits *)
      if Queue.length hot >= !max_configs * 3 / 4 then
        max_configs := !max_configs * 2
    done;

    (!outs, !err)
end

module Hybrid (I : Interpreter) = struct
  let max_configs = 32

  let eval (c : I.sym_config) :
      Encoding.Formula.t list * (string * Interpreter.Source.region) option =
    let w = Queue.create () in
    Queue.push c w;

    let err = ref None in
    let outs = ref [] in
    while Option.is_none !err && not (Queue.is_empty w) do
      let l = Queue.length w in
      let c = Queue.pop w in

      if l >= max_configs then
        match I.concolic_invoke c with
        | Some step_err -> err := Some step_err
        | None -> ()
      else
        match I.step c with
        | Result.Ok step_res -> (
            match step_res with
            | I.Continuation cs' -> Queue.add_seq w (List.to_seq cs')
            | I.End e -> outs := e :: !outs)
        | Result.Error step_err -> err := Some step_err
    done;

    (!outs, !err)
end

module HybridP (I : Interpreter) = struct
  let max_configs = 128

  let eval (c : I.sym_config) :
      Encoding.Formula.t list * (string * Interpreter.Source.region) option =
    let w = Queue.create () in
    Queue.push c w;

    let err = ref None in
    let outs = ref [] in
    while Option.is_none !err && not (Queue.is_empty w) do
      let l = Queue.length w in
      let c = Queue.pop w in

      if l >= max_configs then (
        match I.p_invoke c with
        | Error step_err -> err := Some step_err
        | Ok pc' ->
            outs := pc' :: !outs;
            Queue.add_seq w (Option.to_seq (I.p_finished c pc')))
      else
        match I.step c with
        | Result.Ok step_res -> (
            match step_res with
            | I.Continuation cs' -> Queue.add_seq w (List.to_seq cs')
            | I.End e -> outs := e :: !outs)
        | Result.Error step_err -> err := Some step_err
    done;

    (!outs, !err)
end

module Helper (I : Interpreter) = struct
  module DFS_I = DFS (I)
  module BFS_I = BFS (I)
  module BFS_L_I = BFS_L (I)
  module Half_BFS_I = Half_BFS (I)
  module RS_I = RS (I)
  module Hybrid_I = Hybrid (I)
  module HybridP_I = HybridP (I)

  let helper (inst : Interpreter.Instance.module_inst) (vs : Expression.t list)
      (es : sym_admin_instr list) (sym_m : Concolic.Heap.t) (globs : Globals.t)
      : bool * (string * Interpreter.Source.region) option * float * int =
    let c = I.sym_config inst vs es sym_m globs in

    let eval =
      match !Interpreter.Flags.policy with
      | "depth" -> DFS_I.eval
      | "breadth" -> BFS_I.eval
      | "breadth-l" -> BFS_L_I.eval
      | "half-breadth" -> Half_BFS_I.eval
      | "random" -> RS_I.eval
      | "hybrid" -> Hybrid_I.eval
      | "hybridp" -> HybridP_I.eval
      | _ -> failwith "unreachable"
    in

    let loop_start = Sys.time () in
    let pcs, step_err = eval c in
    let spec, reason, paths =
      match step_err with
      | None -> (true, None, List.length pcs)
      | Some step_err -> (false, Some step_err, List.length pcs)
    in

    let loop_time = Sys.time () -. loop_start in

    (spec, reason, loop_time, paths)
end
