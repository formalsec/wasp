# WebAssembly Symbolic Processor (WASP)

[![Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-blue)](LICENSE)
![Platform](https://img.shields.io/badge/platform-linux%20%7C%20macos-lightgrey)
[![GitHub last commit](https://img.shields.io/github/last-commit/wasp-platform/wasp)](https://github.com/wasp-platform/wasp/commit/main~0)

The WebAssembly Symbolic Processor (WASP), is a symbolic execution engine for
testing Wasm modules, which works directly on Wasm code and was built on top 
of a standard-compliant Wasm reference implementation.

## Build from source


- Install [opam](https://opam.ocaml.org/doc/Install.html).
- Bootstrap the OCaml compiler:

```sh
opam init -y
opam switch create wasp 4.14.0 4.14.0
eval $(opam env)
```

* Then, install the library dependencies:

```sh
git clone https://github.com/wasp-platform/wasp.git
cd wasp
opam install . ./encoding/encoding.opam --deps-only
```

* Build and test:

```sh
dune build
dune runtest
```

* Install `wasp` on your `PATH` by running:

```
dune install
```

## Running WASP

You can call the executable with

```
wasp [option | file ...]
```

#### `wasp: undefined symbol Z3_fixedpoint_pop`

If you encounter this or other Z3 symbol related errors 
add the following line to your shell configuration file:

```sh
# change /default/ if you installed z3 on another version of OCaml
export LD_LIBRARY_PATH="${HOME}/.opam/default/lib/z3/:${LD_LIBRARY_PATH}"
```

On macOS the environment variable should be `DYLD_LIBRARY_PATH`.

#### Converting Modules or Scripts

The option `-o` allows to output module definitions to 
files. Depending on its extension, it'll write out 
the module definition in either S-expression or binary 
format. This option allows to convert between the 
two in both directions. For example:

```
wasp -d module.wast -o module.wasm
wasp -d module.wasm -o module.wast
```
#### Command Line Expressions

The option `-e` allows to provide arbitrary script commands 
directly on the command line. For example:

```
wasp module.wasm -e '(invoke "foo")'
```

#### Additional Details

WASP extends the [WebAssembly Reference Interpreter](https://github.com/WebAssembly/spec/tree/master/interpreter). Hence, all other additional functionalities of the reference interpreter are available in WASP.

