open Prelude
module Flags = Interpreter.Flags

let run_concolic filename unchecked trace timeout workspace no_simplify policy
  queries log =
  let open Wasp.Std.Let_syntax.Result in
  Flags.unchecked := unchecked;
  Flags.trace := trace;
  Flags.timeout := timeout;
  Flags.output := workspace;
  Flags.simplify := no_simplify;
  (* Flags.policy := *)
  Flags.queries := queries;
  Flags.log := log;
  let+ data = Bos.OS.File.read filename in
  if not (Wasp.Run.run_string_concolic data policy) then 1 else 0

let cli =
  let info = Cmdliner.Cmd.info "wasp" ~version:"%%VERSION%%" in
  Cmdliner.Cmd.group info [ Options.cmd_concolic run_concolic ]

let () =
  match Cmdliner.Cmd.eval_value' cli with
  | `Ok result -> (
    match result with
    | Ok n -> exit n
    | Error (`Msg msg) ->
      Fmt.epr "unexpected error: %s@." msg;
      exit 2 )
  | `Exit n -> exit n
