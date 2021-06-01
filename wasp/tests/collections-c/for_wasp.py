#!/usr/bin/env python3

import glob, comby as cby

SRCS = glob.glob('./for-wasp/**/*.c', recursive=True)
SRCS = SRCS + glob.glob('./for-wasp/**/*.h', recursive=True)

PATTERNS = [
        ('#include <gillian-c/gillian-c.h>', '#include "mockups.h"'),
        ("int :[[x]] = __builtin_annot_intval(\"symb_int\", :[[x]]);", \
                "int :[x] = sym_int(\":[x]\");"),
        ("char :[[x]] = __builtin_annot_intval(\"symb_int\", :[[x]]);", \
                "int :[x] = sym_int(\":[x]\");"),
        ("char :[[x]] = (char)__builtin_annot_intval(\"symb_int\", :[[x]]);", \
                "int :[x] = sym_int(\":[x]\");"),
        (':[[type]] X = (:[[type]])__builtin_annot_intval("symb_int", :[[x]])', \
                ":[type] :[x] = sym_int(\":[x]\");"),
        (":[[x]] = __builtin_annot_intval(\"symb_int\", :[[x]]);", \
                ":[x] = sym_int(\":[x]\");"),
        ('*:[[x]] = __builtin_annot_intval("symb_int", *:[[x]]);', \
                ":[x] = sym_int(\":[x]\");"),
        ('ASSERT(:[assertion]);','assert(:[assertion]);'),
        ('ASSUME(:[assertion]);','assume(:[assertion]);'),
        ('ASSUME (:[assertion]);','assume(:[assertion]);')

]

comby = cby.Comby()
for src in SRCS:
    print(f'Transforming {src}...')

    with open(src, 'r') as f:
        data = f.read()

    for p in PATTERNS:
        data = comby.rewrite(data, p[0], p[1])

    with open(src, 'w') as f:
        f.write(data)
