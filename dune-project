(lang dune 3.0)

(name wasp)

(generate_opam_files true)

(source
 (github wasp-platform/wasp))

(authors "WASP Platform")

(maintainers "WASP Platform")

(license LICENSE)

(package
 (name wasp)
 (synopsis "WebAssembly Symbolic Processor (WASP)")
 (description "WASP is a symbolic execution engine for testing and validating Wasm modules.")
 (depends
   batteries
   bos
   cmdliner
   dune
   ocaml
   (ocamlformat :with-dev-setup)
   (ocaml-lsp-server :with-dev-setup)
   pyml
   re2
   (smtml (>= "0.2.4"))
   z3))
