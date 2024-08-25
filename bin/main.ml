open Prelude
module Flags = Interpreter.Flags

let run_concolic filename unchecked trace timeout workspace no_simplify policy
  queries log =
  let open Wasp.Std.Let_syntax.Result in
  Flags.unchecked := unchecked;
  Flags.trace := trace;
  Flags.timeout := timeout;
  (* Need to keep this here because there are references to it? *)
  Flags.output := workspace;
  Flags.simplify := no_simplify;
  (* Flags.policy := *)
  Flags.queries := queries;
  Flags.log := log;
  let testsuite = Fpath.(v workspace / "test_suite") in
  let* _ = Bos.OS.Dir.create ~path:true testsuite in
  let+ data = Bos.OS.File.read filename in
  let _result =
    Wasp.Run.run_string_concolic
      ~testsuite:(Fpath.to_string testsuite)
      ~data policy
  in
  ()

let run_symbolic _filename _unchecked _trace _timeout _workspace _policy
  (* memory *) _queries (* allocs *) _log =
  (* let argspec = *)
  (*   Arg.align *)
  (*     ; ("-u", Arg.Set Flags.unchecked, " unchecked, do not perform validation") *)
  (*     ; ("-h", Arg.Clear Flags.harness, " exclude harness for JS conversion") *)
  (*     ; ("-d", Arg.Set Flags.dry, " dry, do not run program") *)
  (*     ; ("-t", Arg.Set Flags.trace, " trace execution") *)
  (*     ; ( "-v" *)
  (*       , Arg.Unit *)
  (*           (fun () -> *)
  (*             banner (); *)
  (*             exit 0 ) *)
  (*       , " show version" ) *)
  (*     ; ("--timeout", Arg.Set_int Flags.timeout, " time limit (default=900s)") *)
  (*     ; ( "--workspace" *)
  (*       , Arg.Set_string Flags.output *)
  (*       , " directory to output report and test-suite (default=output)" ) *)
  (*     ; ( "--policy" *)
  (*       , Arg.Set_string Flags.policy *)
  (* , " search policy random|depth|breadth|breadth-l|half-breadth (default: \ *)
     (*          random)" ) *)
  (*     ; ( "--encoding" *)
  (*       , Arg.Set_string Flags.encoding *)
  (*       , " encoding policy incremental|batch (default: incremental)" ) *)
  (*     ; ( "--memory" *)
  (*       , Arg.Set_string Flags.memory *)
  (*       , " memory backend map|lazy|tree (default: map)" ) *)
  (*     ; ( "--queries" *)
  (*       , Arg.Set Flags.queries *)
  (*       , " output solver queries in .smt2 format" ) *)
  (*     ; ( "--allocs" *)
  (*       , Arg.Int (fun i -> Flags.fixed_numbers := i :: !Flags.fixed_numbers) *)
  (*       , " add allocation size to be tested on symbolic allocations" ) *)
  (*     ; ("--log", Arg.Set Flags.log, " logs paths and memory") *)
  (*     ] *)
  Fmt.failwith "Symbolic execution has been temporarily disabled"

let cli =
  let info = Cmdliner.Cmd.info "wasp" ~version:"%%VERSION%%" in
  Cmdliner.Cmd.group info
    [ Options.cmd_concolic run_concolic; Options.cmd_symbolic run_symbolic ]

let () =
  match Cmdliner.Cmd.eval_value' cli with
  | `Ok result -> (
    match result with
    | Ok () -> exit Cmdliner.Cmd.Exit.ok
    | Error (`Msg msg) ->
      Fmt.epr "unexpected error: %s@." msg;
      exit 2 )
  | `Exit n -> exit n
