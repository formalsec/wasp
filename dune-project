(lang dune 3.0)

(name wasp)

(generate_opam_files true)

(source
 (github wasp-platform/wasp))

(authors "WASP Platform")

(maintainers "WASP Platform")

(license "Apache-2.0")

(package
 (name wasp)
 (synopsis "WebAssembly Symbolic Processor (WASP)")
 (description "WASP is a symbolic execution engine for testing and validating Wasm modules.")
 (depends
   (ocaml (>= "4.14.0"))
   (base (= "v0.15.1"))
   (core (= "v0.15.1"))
   (core_unix (= "v0.15.1"))
   batteries
   ocamlformat))
