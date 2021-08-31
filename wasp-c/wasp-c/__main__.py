import sys

from pycparser import (
    parse_file,
    c_generator
)
from .visitor import MyVisitor

def main(filename):
    c_gen = c_generator.CGenerator()
    ast = parse_file(
        filename,
        use_cpp=True,
        cpp_path='gcc',
        cpp_args=['-E', r'-Ilib']
    )
    n_ast = MyVisitor().visit(ast)
    c_gen = c_generator.CGenerator()
    n_ast_s = c_gen.visit(n_ast)
    print(n_ast_s)

if __name__ == '__main__':
    main(sys.argv[1])
