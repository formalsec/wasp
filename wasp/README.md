# WebAssembly Symbolic Processor (WASP)

## Documentation

* [Symbolic Instruction Set](doc/symISA.md)

## Installation

You'll need OCaml 4.07 or higher. [OPAM](https://opam.ocaml.org/) 
is the package manager for OCaml. It is the recommended
way to install the OCaml compiler and OCaml packages. 
Simply follow the [OPAM install instructions](https://opam.ocaml.org/doc/Install.html) 
for your distribution.

Then, use opam to install an OCaml compiler

```sh
# environment setup
opam init -y
eval $(opam env)
# install given version of the compiler (4.08.1 - recommended)
opam switch create wasp 4.08.1
eval $(opam env)
```

Lastly, use opam to install the package requirements and the Dune build system

```sh
# OCaml dependencies
opam pin .
```

## Building

Once you have OCaml and Dune, simply do

```sh
dune build
```

You'll get an exacutable named `./_build/install/default/bin/wasp.exe`.
This is a byte code exacutable.

## Running

You can call the executable with

```
wasp [option | file ...]
```
#### `./wasp: undefined symbol Z3_fixedpoint_pop`

If you encounter this or other z3 symbol related errors 
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
./wasp -d module.wast -o module.wasm
./wasp -d module.wasm -o module.wast
```
#### Command Line Expressions

The option `-e` allows to provide arbitrary script commands 
directly on the command line. For example:

```
./wasp module.wasm -e '(invoke "foo")'
```
#### Additional Details

This symbolic processor extends the [WebAssembly Reference Interpreter](https://github.com/WebAssembly/spec/tree/master/interpreter). 
Hence, all other additional functionalities of the interpreter 
are available in WASP.

