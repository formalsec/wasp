import os, threading
from comby import CombyBinary


patterns = [
        (':[[h1]] __VERIFIER_nondet_:[[h2]](:[_])', ':[h1] __VERIFIER_nondet_:[h2](char *)'),
        ('unsigned :[[h1]] __VERIFIER_nondet_u:[[h1]](:[_])', \
                'unsigned :[h1] __VERIFIER_nondet_u:[h1](char *)'),
        ('return __VERIFIER_nondet_:[[h1]](...)', \
                'return __VERIFIER_nondet_:[h1](\"return_:[id()]\")'),

        (':[h1~\w+(\[\s*\w+\s*\])*]:[~\s*]=:[~\s*]__VERIFIER_nondet_:[h2]()', \
                ':[h1] = __VERIFIER_nondet_:[h2](\":[h1]_:[id()]\")'),
        (':[h1~\w+(\[\s*\w+\s*\])*]:[~\s*]=:[~\s*](:[cast]):[~\s*]__VERIFIER_nondet_:[h2]()', \
                ':[h1] = (:[cast]) __VERIFIER_nondet_:[h2](\":[h1]_:[id()]\")'),
        (':[h1~\w+(\[\s*\w+\s*\])*]:[~\s*]=:[~\s*]:[ops]:[~\s*]__VERIFIER_nondet_:[h2]()', \
                ':[h1] = :[ops] __VERIFIER_nondet_:[h2](\":[h1]_:[id()]\")'),
        (':[[h1]] = __VERIFIER_nondet_:[h2]()', ':[h1] = __VERIFIER_nondet_:[h2](\":[h1]_:[id()]\")'),

        ('if:[~\s*](:[~\s*]__VERIFIER_nondet_:[h1]():[~\s*])', \
                'if (__VERIFIER_nondet_:[h1](\"if_:[id()])\"))'),
        (':[[cond]]:[~\s*](:[h2]__VERIFIER_nondet_:[h1]():[h3])', \
                ':[cond] (:[h2]__VERIFIER_nondet_:[h1](\":[cond]_:[id()]\"):[h3])'),
        ('void assume(...) {...}', ''),
        ('void assert(...) {...}', ''),
        ('void abort(...) {...}' , '')

]

dirs = [
        'for-wasp/array-cav19', 
        'for-wasp/array-crafted', 
        'for-wasp/array-examples',
        'for-wasp/array-fpi',
        'for-wasp/array-industry-pattern',
        'for-wasp/array-lopstr16',
        'for-wasp/array-multidimensional',
        'for-wasp/array-patterns',
        'for-wasp/array-programs',
        #'for-wasp/array-memsafety',
        #'for-wasp/array-memsafety-realloc',
        'for-wasp/array-tiling',
        'for-wasp/bitvector',
        'for-wasp/bitvector-loops',
        'for-wasp/bitvector-regression',
        'for-wasp/combinations',
        'for-wasp/float-benchs',
        'for-wasp/float-newlib',
        'for-wasp/floats-cbmc-regression',
        'for-wasp/floats-cdfpl',
        'for-wasp/floats-esbmc-regression',
        'for-wasp/forester-heap',
        'for-wasp/heap-data',
        'for-wasp/list-ext-properties',
        'for-wasp/list-ext2-properties',
        'for-wasp/list-ext3-properties',
        'for-wasp/list-properties',
        'for-wasp/list-simple',
        'for-wasp/locks',
        'for-wasp/loop-crafted',
        'for-wasp/loop-floats-scientific-comp',
        'for-wasp/loop-industry-pattern',
        'for-wasp/loop-invariants',
        'for-wasp/loop-invgen',
        'for-wasp/loop-lit',
        'for-wasp/loop-new',
        'for-wasp/loop-simple',
        'for-wasp/loop-zilu',
        #'for-wasp/loops',
        #'for-wasp/loops-crafted-1'
        #'for-wasp/ntdrivers',
        'for-wasp/ntdrivers-simplified',
        'for-wasp/openssl',
        'for-wasp/openssl-simplified',
        'for-wasp/recursive',
        'for-wasp/recursive-simple',
        'for-wasp/recursive-with-pointer',
        'for-wasp/reducercommutativity',
        'for-wasp/verifythis',
        'for-wasp/xcsp',
        'for-wasp/nla-digbench',
        'for-wasp/nla-digbench-scaling',
        'for-wasp/psyco',
        'for-wasp/systemc',
        'for-wasp/termination-crafted',
        'for-wasp/termination-crafted-lit',
        #'for-wasp/memsafety',
        #'for-wasp/memsafety-bftpd',
        #'for-wasp/memsafety-ext',
        #'for-wasp/memsafety-ext2',
        'for-wasp/termination-numeric'
]

dirs = [ 'for-wasp/recursive-with-pointer' ]

nthreads = 4

src = []
for d in dirs:
    src = src + list( \
            map(lambda f : f'{d}/{f.name}', \
                filter(lambda f : f.name.endswith('.c'), \
                       os.scandir(d))))

def thread_main(id, vec, n):
    length = len(vec)
    low    = int((id * length) / n)
    high   = int(((id + 1) * length) / n)

    comby  = CombyBinary()
    for i in range(low, high):
        path = vec[i]
        print(f'Transforming {path}...')

        with open(path, 'r') as f:
            data = f.read()

        for patt in patterns:
            data = comby.rewrite(data, patt[0], patt[1], language='.c')

        with open(path, 'w') as f:
            f.write(data)

thread_main(0, src, 1)
#for i in range(0, nthreads):
#    t = threading.Thread(target=thread_main, args=(i, src, nthreads,))
#    t.start()
