let main filename = Format.printf "%a@." Fpath.pp filename

let cli =
  let open Cmdliner in
  let info = Cmd.info "wasp" ~version:"%%VERSION%%" in
  Cmd.v info Term.(const main $ Options.file0)

let () = exit (Cmdliner.Cmd.eval cli)
