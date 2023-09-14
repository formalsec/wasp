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
 (depends base batteries ocamlformat))

(package
 (name waspc)
 (synopsis "")
 (description "")
 (depends ocaml dune re2 bos pyml cmdliner))
