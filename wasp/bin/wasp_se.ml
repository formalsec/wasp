open Interpreter

let name = "WebAssembly Static Executor"
let version = "v0.1"

let configure () =
  Import.register (Utf8.decode "spectest") Spectest.lookup;
  Import.register (Utf8.decode "env") Env.lookup

let banner () = print_endline (name ^ " " ^ version)
let usage = "Usage: " ^ name ^ " [option] [file ...]"
let args = ref []
let add_arg source = args := !args @ [ source ]
let quote s = "\"" ^ String.escaped s ^ "\""

let argspec =
  Arg.align
    [
      ( "-",
        Arg.Set Flags.interactive,
        " run interactively (default if no files given)" );
      ("-e", Arg.String add_arg, " evaluate string");
      ( "-i",
        Arg.String (fun file -> add_arg ("(input " ^ quote file ^ ")")),
        " read script from file" );
      ( "-o",
        Arg.String (fun file -> add_arg ("(output " ^ quote file ^ ")")),
        " write module to file" );
      ("-s", Arg.Set Flags.print_sig, " show module signatures");
      ("-u", Arg.Set Flags.unchecked, " unchecked, do not perform validation");
      ("-h", Arg.Clear Flags.harness, " exclude harness for JS conversion");
      ("-d", Arg.Set Flags.dry, " dry, do not run program");
      ("-t", Arg.Set Flags.trace, " trace execution");
      ( "-v",
        Arg.Unit
          (fun () ->
            banner ();
            exit 0),
        " show version" );
      ("--timeout", Arg.Set_int Flags.timeout, " time limit (default=900s)");
      ( "--workspace",
        Arg.Set_string Flags.output,
        " directory to output report and test-suite (default=output)" );
      ( "-m",
        Arg.Set_int Flags.inst_limit,
        " maximum instr interpreted during a model" );
      ( "--policy",
        Arg.Set_string Flags.policy,
        " search policy random|depth|breadth|breadth-l|half-breadth (default: \
         random)" );
      ( "--encoding",
        Arg.Set_string Flags.encoding,
        " encoding policy incremental|batch (default: incremental)" );
      ( "--memory",
        Arg.Set_string Flags.memory,
        " memory backend map|lazy|tree (default: map)" );
      ( "--queries",
        Arg.Set Flags.queries,
        " output solver queries in .smt2 format" );
      ( "--allocs",
        Arg.Int (fun i -> Flags.fixed_numbers := i :: !Flags.fixed_numbers),
        " add allocation size to be tested on symbolic allocations" );
    ]

let () =
  Printexc.record_backtrace true;
  try
    configure ();
    Arg.parse argspec (fun file -> add_arg ("(input " ^ quote file ^ ")")) usage;
    List.iter (fun arg -> if not (Wasp.Run.run_string_se arg) then exit 1) !args;
    if !args = [] then Flags.interactive := true;
    if !Flags.interactive then (
      Flags.print_sig := true;
      banner ();
      Wasp.Run.run_stdin ())
  with exn ->
    flush_all ();
    prerr_endline
      (Sys.argv.(0) ^ ": uncaught exception " ^ Printexc.to_string exn);
    Printexc.print_backtrace stderr;
    exit 2
