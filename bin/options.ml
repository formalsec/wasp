open Cmdliner

let path = ((fun s -> `Ok (Fpath.v s)), Fpath.pp)

let file0 =
  let doc = "$(docv) is the command input" in
  Arg.(required & pos 0 (some path) None & info [] ~doc ~docv:"FILE")

let unchecked =
  let doc = "Unchecked, do not perform validation" in
  Arg.(value & flag & info [ "u"; "unchecked" ] ~doc)

let trace =
  let doc = "Trace execution" in
  Arg.(value & flag & info [ "t"; "trace" ] ~doc)

let timeout =
  let doc = "Time limit" in
  Arg.(value & opt int ~-1 & info [ "timeout" ] ~doc)

let workspace =
  let doc = "Directory to output report and testsuite (default=wasp-out)" in
  Arg.(value & opt string "wasp-out" & info [ "workspace" ] ~doc)

let no_simplify =
  let doc = "Don't perform algebraic simplifications of symbolic expressions" in
  Arg.(value & flag & info [ "no-simplify" ] ~doc)

let policy_conv =
  Arg.enum
    [ ("random", Concolic.Eval.Random)
    ; ("depth", Concolic.Eval.Depth)
    ; ("breadth", Concolic.Eval.Breadth)
    ]

let policy =
  let doc = "Search policy random|depth|breadth (default=random)" in
  Arg.(value & opt policy_conv Concolic.Eval.Random & info [ "policy" ] ~doc)

let queries =
  let doc = "Output solver queries in .smt2 format" in
  Arg.(value & flag & info [ "queries" ] ~doc)

let log =
  let doc = "Logs paths and memory" in
  Arg.(value & flag & info [ "log" ] ~doc)

let cmd_concolic run =
  let doc = "Performs concolic execution" in
  let man =
    [ `P "Concolically executes a WebAssembly program in textual format (.wat)"
    ]
  in
  let info = Cmd.info "concolic" ~doc ~man in
  Cmd.v info
    Term.(
      const run $ file0 $ unchecked $ trace $ timeout $ workspace $ no_simplify
      $ policy $ queries $ log )

let cmd_symbolic run =
  let doc = "Performs symbolic execution" in
  let man =
    [ `P "Symbolically executes a WebAssembly program in textual format (.wat)"
    ]
  in
  let info = Cmd.info "symbolic" ~doc ~man in
  Cmd.v info
    Term.(
      const run $ file0 $ unchecked $ trace $ timeout $ workspace $ policy
      $ queries $ log )
