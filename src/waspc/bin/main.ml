open Waspc
open Bos

(* Just blowup for now, maybe bind later? *)
let ( let* ) r f = match r with Error (`Msg e) -> failwith e | Ok v -> f v

let pre_patterns : (Re2.t * string) array =
  Array.map
    (fun (regex, template) -> (Re2.create_exn regex, template))
    [| ( "void\\s+reach_error\\(\\)\\s*\\{.*\\}"
       , "void reach_error() { __WASP_assert(0); }" )
       (* ugly: Hack to solve duplicate errors on compilation *)
     ; ("void\\s+(assert|assume)\\(", "void old_\\1(")
    |]

let post_patterns : (Re2.t * string) array =
  Array.map
    (fun (regex, template) -> (Re2.create_exn regex, template))
    [| ("call \\$__WASP_(assert|assume)", "sym_\\1")
     ; ("call \\$(assume_abort_if_not|assume_cycle_if_not|assume)", "sym_assume")
     ; ("call \\$__VERIFIER_nondet_bool", "i32.const 0\n\tb32.symbolic")
     ; ( "call \\$__(VERIFIER_nondet_(u?(char|short|int128|int|long)))"
       , "(i32.symbolic (i32.const 0))" )
     ; ("call \\$__WASP_symb_int", "i32.symbolic")
     ; ("call \\$__WASP_symb_long", "i64.symbolic")
     ; ("call \\$__WASP_symb_float", "f32.symbolic")
     ; ("call \\$__WASP_symb_double", "f64.symbolic")
     ; ("call \\$__VERIFIER_nondet_float", "(f32.symbolic (i32.const 0))")
     ; ("call \\$__VERIFIER_nondet_double", "(f64.symbolic (i32.const 0))")
     ; ("call \\$__WASP_alloc", "alloc")
     ; ("call \\$__WASP_dealloc", "free")
     ; ("call \\$__WASP_is_symbolic", "is_symbolic")
     ; ("call \\$__WASP_print_stack", "print_stack")
     ; ("call \\$__WASP_print_pc", "print_pc")
     ; ("call \\$and_", "i32.__logand")
     ; ("call \\$or_", "i32.__logor")
     ; ("call \\$ite", "__ternary_op")
     ; ("anyfunc", "funcref")
     ; ("\\(elem \\(;0;\\) \\(i32.const 1\\) func", "(elem (;0;) (i32.const 1)")
    |]

let patch_with_regex (file_data : string) ~patterns : string =
  Array.fold_left
    (fun data (regex, template) -> Re2.rewrite_exn regex ~template data)
    file_data patterns

let patch_gcc_ext (file_data : string) : string =
  String.concat "\n"
    [ "#define __attribute__(x)"
    ; "#define __extension__"
    ; "#define __restrict"
    ; "#define __inline"
    ; "#include <wasp.h>"
    ; "#include <assert.h>"
    ; file_data
    ]

let instrument_file (file : Fpath.t) (includes : string list) =
  Log.debug "instrumenting ...@.";
  let* data = OS.File.read file in
  let data = patch_gcc_ext data |> patch_with_regex ~patterns:pre_patterns in
  try
    Py.initialize ();
    let data = Instrumentor.instrument data includes in
    Py.finalize ();
    data
  with Py.E (err_type, _) as _e ->
    Log.debug "      warning : exception \"%s\"@."
      (Py.Object.to_string err_type);
    data

let clang flags out_file file =
  Cmd.(v "clang" %% flags % "-o" % p out_file % p file)

let opt file = Cmd.(v "opt" % "-O1" % "-o" % p file % p file)

let llc bc obj =
  let flags = Cmd.of_list [ "-O1"; "-march=wasm32"; "-filetype=obj"; "-o" ] in
  Cmd.(v "llc" %% flags % p obj % p bc)

let ld flags out_file file =
  let* ld_path = OS.Env.req_var "LD_PATH" in
  let libc = Fpath.(v ld_path / "libc.wasm") in
  Cmd.(v "wasm-ld" %% flags % "-o" % p out_file % p libc % p file)

let wasm2wat binary output = Cmd.(v "wasm2wat" % p binary % "-o" % p output)

let compile_file (file : Fpath.t) ~(includes : string list) =
  Log.debug "    compiling ...@.";
  let cflags =
    let includes = Cmd.of_list ~slip:"-I" includes in
    let warnings =
      Cmd.of_list
        [ "-Wno-int-conversion"
        ; "-Wno-pointer-sign"
        ; "-Wno-string-plus-int"
        ; "-Wno-implicit-function-declaration"
        ; "-Wno-incompatible-library-redeclaration"
        ; "-Wno-incompatible-function-pointer-types"
        ; "-Wno-incompatible-pointer-types"
        ]
    in
    Cmd.(
      of_list [ "-g"; "-emit-llvm"; "--target=wasm32"; "-m32"; "-c" ]
      %% warnings %% includes )
  in
  let ldflags entry =
    Cmd.(
      of_list [ "-z"; "stack-size=1073741824"; "--no-entry" ]
      % ("--export=" ^ entry) )
  in
  let file_bc = Fpath.(file -+ ".bc") in
  let file_obj = Fpath.(file -+ ".o") in
  let file_wasm = Fpath.(file -+ ".wasm") in
  let file_wat = Fpath.(file -+ ".wat") in
  let* _ = OS.Cmd.run @@ clang cflags file_bc file in
  let* _ = OS.Cmd.run @@ opt file_bc in
  let* _ = OS.Cmd.run @@ llc file_bc file_obj in
  let* _ = OS.Cmd.run @@ ld (ldflags "__original_main") file_wasm file_obj in
  let* _ = OS.Cmd.run @@ wasm2wat file_wasm file_wat in
  file_wat

let run_file file output =
  Log.debug "      running2 ...@.";
  (* Set flags in the reference interpreter *)
  Interpreter.Flags.trace := true;
  Interpreter.Flags.output := Fpath.to_string output;
  (* Create command sequence for reference interpreter *)
  let cmds =
    [ Format.sprintf "(input \"%s\")" (Fpath.to_string file)
    ; Format.sprintf "(invoke \"__original_main\")"
    ]
  in
  List.iter (fun cmd -> if not @@ Wasp.Run.run_string_se cmd then exit 1) cmds

let main debug output includes files =
  Log.on_debug := debug;
  let output = Fpath.v output in
  let* _ = OS.Dir.create output in
  List.iter
    (fun file ->
      let* file = OS.File.must_exist (Fpath.v file) in
      let file_data = instrument_file file includes in
      let tmp_file_path = Fpath.(output / "instrumented.c") in
      let* _ = OS.File.write tmp_file_path file_data in
      let wat_file_path = compile_file tmp_file_path ~includes in
      let* file_data = OS.File.read wat_file_path in
      let file_data' = patch_with_regex file_data ~patterns:post_patterns in
      let* _ = OS.File.write wat_file_path file_data' in
      run_file wat_file_path output )
    files

let debug =
  let doc = "debug mode" in
  Cmdliner.Arg.(value & flag & info [ "debug" ] ~doc)

let output =
  let doc = "write results to dir" in
  Cmdliner.Arg.(value & opt string "wasp-out" & info [ "output"; "o" ] ~doc)

let includes =
  let doc = "headers path" in
  Cmdliner.Arg.(value & opt_all string [] & info [ "I" ] ~doc)

let files =
  let doc = "source files" in
  Cmdliner.Arg.(value & pos 0 (list ~sep:' ' string) [] & info [] ~doc)

let cli =
  let open Cmdliner in
  let doc = "wasp-c" in
  let man = [ `S Manpage.s_bugs; `P "Email them to TODO" ] in
  let info = Cmd.info "waspc" ~doc ~man in
  Cmd.v info Term.(const main $ debug $ output $ includes $ files)

let () = exit @@ Cmdliner.Cmd.eval cli
