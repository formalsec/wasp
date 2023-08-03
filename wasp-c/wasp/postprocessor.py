import re

patterns = [
    # Test-Comp Patterns
    (r"call \$assume$", "sym_assume"),
    (r"call \$assume_abort_if_not$", "sym_assume"),
    (r"call \$assume_cycle_if_not$", "sym_assume"),
    (r"call \$assert", "sym_assert"),
    (r"call \$__VERIFIER_nondet_bool", "i32.const 0\nb32.symbolic"),
    (r"call \$__VERIFIER_nondet_char", "i32.const 0\ni32.symbolic"),
    (r"call \$__VERIFIER_nondet_uchar", "i32.const 0\ni32.symbolic"),
    (r"call \$__VERIFIER_nondet_short", "i32.const 0\ni32.symbolic"),
    (r"call \$__VERIFIER_nondet_ushort", "i32.const 0\ni32.symbolic"),
    (r"call \$__VERIFIER_nondet_int128", "i32.const 0\ni64.symbolic"),
    (r"call \$__VERIFIER_nondet_uint128", "i32.const 0\ni64.symbolic"),
    (r"call \$__VERIFIER_nondet_int", "i32.const 0\ni32.symbolic"),
    (r"call \$__VERIFIER_nondet_uint", "i32.const 0\ni32.symbolic"),
    (r"call \$__VERIFIER_nondet_long", "i32.const 0\ni32.symbolic"),
    (r"call \$__VERIFIER_nondet_ulong", "i32.const 0\ni32.symbolic"),
    (r"call \$__VERIFIER_nondet_float", "i32.const 0\nf32.symbolic"),
    (r"call \$__VERIFIER_nondet_double", "i32.const 0\nf64.symbolic"),
    # Generic WASP-C Patterns
    (r"call \$__WASP_alloc", "alloc"),
    (r"call \$__WASP_dealloc", "free"),
    (r"call \$__WASP_assume", "sym_assume"),
    (r"call \$__WASP_assert", "sym_assert"),
    (r"call \$__WASP_symb_int", "i32.symbolic"),
    (r"call \$__WASP_symb_long", "i64.symbolic"),
    (r"call \$__WASP_symb_float", "f32.symbolic"),
    (r"call \$__WASP_symb_double", "f64.symbolic"),
    (r"call \$__WASP_is_symbolic", "is_symbolic"),
    (r"call \$__WASP_print_stack", "print_stack"),
    (r"call \$__WASP_print_pc", "print_pc"),
    (r"call \$__logand", "i32.__logand"),
    (r"call \$__logor", "i32.__logor"),
    (r"call \$__ternary", "__ternary_op"),
    ("anyfunc", "funcref"),
    ("\(elem \(;0;\) \(i32.const 1\) func", "(elem (;0;) (i32.const 1)")
]

def sub_patterns(line):
    for (pattern, repl) in patterns:
        line = re.sub(pattern, repl, line)
    return line

def process(text):
    lines = text.splitlines()
    return "\n".join([sub_patterns(line) for line in lines])
