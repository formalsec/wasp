import re

patterns = [
    # Test-Comp Patterns
    (r'call \$assume$', 'sym_assume'),
    (r'call \$assume_abort_if_not$', 'sym_assume'),
    (r'call \$assume_cycle_if_not$', 'sym_assume'),
    ('call \$assert', 'sym_assert'),
    ('call \$__VERIFIER_nondet_bool', 'b32.symbolic'),
    ('call \$__VERIFIER_nondet_char', 'i32.symbolic'),
    ('call \$__VERIFIER_nondet_uchar', 'i32.symbolic'),
    ('call \$__VERIFIER_nondet_short', 'i32.symbolic'),
    ('call \$__VERIFIER_nondet_ushort', 'i32.symbolic'),
    ('call \$__VERIFIER_nondet_int', 'i32.symbolic'),
    ('call \$__VERIFIER_nondet_uint', 'i32.symbolic'),
    ('call \$__VERIFIER_nondet_long', 'i32.symbolic'),
    ('call \$__VERIFIER_nondet_ulong', 'i32.symbolic'),
    ('call \$__VERIFIER_nondet_float', 'f32.symbolic'),
    ('call \$__VERIFIER_nondet_double', 'f64.symbolic'),
    # Generic WASP-C Patterns
    ('call \$__WASP_alloc', 'alloc'),
    ('call \$__WASP_dealloc', 'free'),
    ('call \$__WASP_assume', 'sym_assume'),
    ('call \$__WASP_assert', 'sym_assert'),
    ('call \$__WASP_symb_int', 'i32.symbolic'),
    ('call \$__WASP_symb_long', 'i64.symbolic'),
    ('call \$__WASP_symb_float', 'f32.symbolic'),
    ('call \$__WASP_symb_double', 'f64.symbolic'),
    ('call \$__WASP_is_symbolic', 'is_symbolic'),
    ('call \$__logand', 'i32.__logand'),
    ('call \$__logor', 'i32.__logor'),
    ('call \$__ternary', '__ternary_op'),
    ('anyfunc', 'funcref'),
    ('\(elem \(;0;\) \(i32.const 1\) func', '(elem (;0;) (i32.const 1)')
]

def sub_patterns(line):
    for (pattern, repl) in patterns:
        line = re.sub(pattern, repl, line)
    return line

def process(text):
    lines = text.splitlines()
    return '\n'.join([sub_patterns(line) for line in lines])
