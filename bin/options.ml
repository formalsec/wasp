open Cmdliner

let path = ((fun s -> `Ok (Fpath.v s)), Fpath.pp)

let file0 =
  let doc = "input file to analyse" in
  Arg.(required & pos 0 (some path) None & info [] ~doc ~docv:"FILE")
