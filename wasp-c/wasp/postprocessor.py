import re

patterns = [
    (r'call \$__WASP_alloc', 'alloc'),
    (r'call \$__WASP_dealloc', 'free'),
    (r'call \$__WASP_assume', 'sym_assume'),
    (r'call \$__WASP_assert', 'sym_assert'),
    (r'call \$__WASP_symb_int', 'i32.symbolic'),
    (r'call \$__WASP_symb_long', 'i64.symbolic'),
    (r'call \$__WASP_symb_float', 'f32.symbolic'),
    (r'call \$__WASP_symb_double', 'f64.symbolic'),
    (r'call \$__WASP_is_symbolic', 'is_symbolic'),
    (r'call \$__logand', 'i32.__logand'),
    (r'call \$__logor', 'i32.__logor'),
    ('anyfunc', 'funcref'),
    (r'\(elem \(;0;\) \(i32.const 1\) func', '(elem (;0;) (i32.const 1)')
]

def sub_patterns(line):
    for (pattern, repl) in patterns:
        line = re.sub(pattern, repl, line)
    return line

def process(text):
    lines = text.splitlines()
    return '\n'.join([sub_patterns(line) for line in lines])
