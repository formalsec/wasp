warnings = [
    '-Wno-parentheses-equality',
    '-Wno-attributes',
    '-Wno-return-type',
    '-Wno-int-conversion',
    '-Wno-incompatible-pointer-types',
    '-Wno-incompatible-function-pointer-types',
    '-Wno-pointer-sign',
    '-Wno-bitfield-constant-conversion',
    '-Wno-implicit-function-declaration'
]

includes = [
    '-Ilib'
]

compile_cmd = [
    'clang',
    '-emit-llvm',
    '-g',
    '-O0',
    '-ffreestanding',
    '--target=wasm32',
    '-c',
    '-m32',
    '-fbracket-depth=512'
]

opt_cmd = lambda x : [
    'opt',
    '-O1',
    x,
    '-o',
    x
]
