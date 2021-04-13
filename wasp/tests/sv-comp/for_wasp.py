import os
from comby import Comby
from functools import reduce

match = [
            (':[[h1]] __VERIFIER_nondet_:[[h1]](:[_])', ':[h1] __VERIFIER_nondet_:[h1](char *)'),
            ('unsigned :[[h1]] __VERIFIER_nondet_u:[[h1]]()', 'unsigned :[h1] __VERIFIER_nondet_u:[h1](char *)'),
            (':[h1~\w+(\[\w+\])?]:[~\s*]=:[~\s*]__VERIFIER_nondet_:[h2]()', ':[h1] = __VERIFIER_nondet_:[h2](\":[h1]\")')
        ]


dirs = ['for-wasp/array-cav19', 'for-wasp/array-crafted']

src = []
for d in dirs:
    src = src + list( \
            map(lambda f : f'{d}/{f.name}', \
                filter(lambda f : f.name.endswith('.c'), \
                       os.scandir(d))))

comby = Comby()
for path in src:
    print(f'Transforming {path}...')
    with open(path, 'r') as f:
        data = f.read()
        for m in match:
            data = comby.rewrite(data, m[0], m[1])

    with open(path, 'w') as f:
        f.write(data)
