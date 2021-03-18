# WebAssembly Symbolic Processor (WASP)

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
opam switch create 4.08.1
eval $(opam env)
```

Lastly, use opam to install the package requirements

```sh
# OCaml dependencies
opam install -y extlib batteries z3=4.8.1
```

## Building

Once you have OCaml, simply do

```sh
make
```

You'll get an exacutable named `./wasp`. This is a byte
code exacutable.

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

## Symbolic Instruction Set

Examples of symbolically-ready `.wast` scripts are available 
in [tests](tests/). Note that some instructions were added in order 
to allow symbolic execution, such as:

* `(duplicate)`:
  * Duplicate the top value in the stack.
* `(sym_int{32,64} <var_name>)`:
  * Creates a symbolic variable and puts its value on top of 
    the stack. If the variable already exists in the symbolic 
    store, the previous value is used.
* `(sym_float{32,64} <var_name>)`:
  * Creates a symbolic variable and puts its value on top of 
    the stack. If the variable already exists in the symbolic 
    store, the previous value is used.
* `(get_sym_int{32,64} <var_name>)`: 
  * Retrieves from the symbolic store the value associated 
    with the variable and puts it on top of the stack.
* `(get_sym_float{32,64} <var_name>)`:
  * Retrieves from the symbolic store the value associated 
    with the variable and puts it on top of the stack.
* `(sym_assume)`: 
  * Assumes the symbolic expression associated with the 
    value on top of the stack.
* `(sym_assert)`: 
  * Asserts the symbolic expression associated with the 
    value on top of the stack. 
