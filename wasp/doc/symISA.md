# Symbolic Instruction Set (OUTDATED)

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
