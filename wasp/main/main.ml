let name = "WebAssembly Symbolic Processor"
let version = "v0.2"

let configure () =
  Import.register (Utf8.decode "spectest") Spectest.lookup;
  Import.register (Utf8.decode "env") Env.lookup

let banner () =
  print_endline (name ^ " " ^ version)

let usage = "Usage: " ^ name ^ " [option] [file ...]"

let args = ref []
let add_arg source = args := !args @ [source]

let quote s = "\"" ^ String.escaped s ^ "\""

let argspec = Arg.align
[
  "-", Arg.Set Flags.interactive,
    " run interactively (default if no files given)";
  "-e", Arg.String add_arg, " evaluate string";
  "-i", Arg.String (fun file -> add_arg ("(input " ^ quote file ^ ")")),
    " read script from file";
  "-o", Arg.String (fun file -> add_arg ("(output " ^ quote file ^ ")")),
    " write module to file";
  "-w", Arg.Int (fun n -> Flags.width := n),
    " configure output width (default is 80)";
  "-s", Arg.Set Flags.print_sig, " show module signatures";
  "-u", Arg.Set Flags.unchecked, " unchecked, do not perform validation";
  "-h", Arg.Clear Flags.harness, " exclude harness for JS conversion";
  "-d", Arg.Set Flags.dry, " dry, do not run program";
  "-t", Arg.Set Flags.trace, " trace execution";
  "-v", Arg.Unit (fun () -> banner (); exit 0), " show version";
  "-m", Arg.Set_int Flags.inst_limit, " maximum instr interpreted during a model";
  "-b", Arg.Set Flags.branches, " ignore assertion failures to cover more paths";
  "--timeout", Arg.Set_int Flags.timeout, " time limit (default=900s)";
  "--workspace", Arg.Set_string Flags.output,
    " directory to output report and test-suite (default=output)";
  "--smt-assume", Arg.Set Flags.smt_assume,
    " use the solver to progress in the assume rule";
  "--no-simplify", Arg.Clear Flags.simplify,
    " do not perform algebraic simplifications of symbolic expressions";
  "--policy", Arg.Set_string Flags.policy,
    " search policy random|depth|breadth (default: random)";
  "--queries", Arg.Set Flags.queries, " output solver queries in .smt2 format";
]

let () =
  Printexc.record_backtrace true;
  try
    configure ();
    Arg.parse argspec
      (fun file -> 
        (*Ranges.save_useful_lines file; *)
        Coverage.record_loc file;
        add_arg ("(input " ^ quote file ^ ")")) usage;
    List.iter (fun arg -> if not (Symrun.run_string arg) then exit 1) !args; (*  Changed to run symbolically  *)
    if !args = [] then Flags.interactive := true;
    if !Flags.interactive then begin
      Flags.print_sig := true;
      banner ();
      Symrun.run_stdin ()
    end
  with exn ->
    flush_all ();
    prerr_endline
      (Sys.argv.(0) ^ ": uncaught exception " ^ Printexc.to_string exn);
    Printexc.print_backtrace stderr;
    exit 2
