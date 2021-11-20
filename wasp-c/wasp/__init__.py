from __future__ import print_function

import os
import sys
import shutil
import argparse
import subprocess

from wasp import info
from wasp import logger as logging
from wasp import visitor as pre
from wasp import postprocessor as post
from wasp import execution as exe

def get_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog=info.__NAME__,
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )

    parser.add_argument(
        '--version', 
        '-v', 
        action='version', 
        version=f'version {info.__VERSION__}'
    )

    parser.add_argument(
        '--output',
        '-o',
        dest='output_dir',
        action='store',
        default='output',
        help='output directory to write to',
    )

    parser.add_argument(
        '--include',
        '-I',
        dest='includes',
        action='append',
        default=[],
        help='include headers path',
    )

    parser.add_argument(
        '--source',
        '-S',
        dest='source',
        action='store',
        default='',
        help='lib source code'
    )

    parser.add_argument(
        '--verbose',
        dest='verbose',
        action='store_true',
        default=False,
        help='show messages verbose',
    )
 
    parser.add_argument('file', help='file to analyse')

    return parser

def parse(argv: list[str]) -> argparse.Namespace:
    parser = get_parser()
    return parser.parse_args(argv)

def preprocess_file(input_file: str, args: list[str], output_file: str) -> int:
    logging.debug(f'preprocess_file:input_file={input_file}' \
            f', output_file={output_file}')
    harness = pre.process(input_file, args)
    with open(output_file, 'w') as file:
        file.write(harness)
    return 0

def compile_file(output_dir: str, root_dir: str, src_code: str, \
        filename: str) -> int:
    logging.debug(f'compile_file:output_dir={output_dir}' \
            f', root_dir={root_dir}, filename={filename}')

    bin_dir = os.path.join(root_dir, 'bin')
    lib_dir = os.path.join(root_dir, 'lib')

    src_make = os.path.join(root_dir, 'makefiles/Makefile.main')
    dst_make = os.path.join(output_dir, 'Makefile')
    logging.debug(f'compile_file:cp {src_make} {dst_make}')
    shutil.copyfile(src_make, dst_make)

    libc = os.path.join(bin_dir, 'libc.a')
    logging.debug(f'compile_file:make -C {output_dir} LIBC={libc}' \
            f' HEADERS={lib_dir}')
    subprocess.call([
        'make',
        '-C',
        output_dir,
        f'LIBC={libc}',
        f'HEADERS={lib_dir}',
        f'OTHER_CODE={src_code}'
    ])
    return 0

def postprocess_file(input_file: str) -> int:
    logging.debug(f'postprocess_file:input_file={input_file}')
    test = post.process(input_file)
    with open(input_file, 'w') as file:
        file.writelines(test)
    return 0

def main(root_dir: str, argv=None) -> int:
    if argv is None:
        argv = sys.argv[1:]
    args = parse(argv)

    if args.verbose:
        logging.init(logging.DEBUG) 
    else:
        logging.init(logging.INFO)

    if not os.path.exists(args.output_dir):
        logging.debug(f'main:mkdir -p \'{args.output_dir}\'')
        os.makedirs(args.output_dir)

    if not os.path.exists(args.file):
        logging.error(f'main:File \'{args.file}\' not found')
        return -1

    args.includes.append(os.path.join(root_dir, 'lib'))
    includes = ['-I'+lib for lib in args.includes]
    harness = os.path.join(args.output_dir, 'harness.c')
    if not preprocess_file(args.file, includes, harness) == 0:
        logging.error(f'main:Preprocessing failed')
        return -1

    if not compile_file(args.output_dir, root_dir, args.source, \
            harness) == 0:
        logging.error(f'main:Compilation failed')
        return -1

    wasm_harness = os.path.splitext(harness)[0] + '.wat'
    if not postprocess_file(wasm_harness) == 0:
        logging.error(f'main:Postprocessing failed')
        return -1

    # run WASP
    analyser = exe.WASP()
    res = analyser.run(wasm_harness, args.output_dir)
    if res.crashed:
        logging.error(f'main:Wasp crashed')
        return -1
    if res.timeout:
        logging.error(f'main:Wasp timeout')
        return -1
    print(res.stdout)
    return 0
