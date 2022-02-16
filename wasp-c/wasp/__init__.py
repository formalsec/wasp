import os
import sys
import shutil
import logging
import argparse
import subprocess

from wasp import info

from wasp import logger
from wasp import visitor as pre
from wasp import postprocessor as post

from wasp.execution import WASP

log = logging.getLogger(__name__)

def get_parser():
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

    parser.add_argument(
        '--rm-boolops',
        dest='boolops',
        action='store_true',
        default=False,
        help='remove short-circuit evaluation'
    )

    parser.add_argument('file', help='file to analyse')

    return parser

def parse(argv):
    parser = get_parser()
    return parser.parse_args(argv)

def preprocess_file(src_file, dst_file, includes, boolops):
    log.debug(f'Processing \'{src_file}\'...')
    try:
        pre.process_file(src_file, dst_file, includes, boolops)
    except pre.ParsingError as e:
        log.error('ParsingError: ' + e.message)
        return 1
    log.debug(f'Created \'{dst_file}\'.')
    return 0

def configure(output_dir, root_dir, src_code, includes):
    log.debug(f'Configuring compilation...')

    # Copy `Makefile' to `output_dir'
    src_make = os.path.join(root_dir, 'makefiles', 'Makefile.main')
    dst_make = os.path.join(output_dir, 'Makefile')
    log.debug(f'... Copy \'{src_make}\' to \'{dst_make}\'.')
    shutil.copyfile(src_make, dst_make)

    # Create `Makefile.config'
    libs = os.path.join(root_dir, 'bin')
    incl = os.path.join(root_dir, 'lib')
    conf = os.path.join(output_dir, 'Makefile.config')
    log.debug(f'... Using static libc in \'{libs}\'.')
    log.debug(f'... Using static libc includes in \'{incl}\'.')
    log.debug(f'... Using additional includes: {includes}')
    log.debug(f'... Using additional sources in \'{src_code}\'.')
    with open(conf, 'w') as f:
        f.write(f'LIBC_DIR = {libs}\n')
        f.write(f'LIBC_INC = {incl}\n')
        for inc in includes:
            f.write(f'INCLUDES += -I{inc}\n')
        f.write(f'OTHER_CODE = {src_code}\n')

    log.debug(f'Created \'{conf}\'.')

def compile_sources(sources):
    log.debug(f'Compiling sources in \'{sources}\'...')
    try:
        result = subprocess.run(
            ['make', '-C', sources],
            text=True,
            check=True,
            capture_output=True
        )
    except subprocess.CalledProcessError as e:
        log.error(e.stdout)
        log.error(e.stderr)
        return -1
    log.debug(f'Compilation done.')
    return 0

def postprocess_file(file):
    log.debug(f'Processing Wasm module \'{file}\'...')
    
    with open(file, 'r') as f:
        text = f.read()

    n_text = post.process(text)

    with open(file, 'w') as f:
        f.write(n_text)
    return 0

def main(root_dir, argv=None):
    if argv is None:
        argv = sys.argv[1:]
    args = parse(argv)

    if args.verbose:
        logger.init(log, logging.DEBUG) 
    else:
        logger.init(log, logging.INFO)

    if not os.path.exists(args.output_dir):
        log.debug(f'Creating directory \'{args.output_dir}\'...')
        os.makedirs(args.output_dir)

    if not os.path.exists(args.file):
        log.error(f'Input file \'{args.file}\' not found!')
        return -1

    log.info('Setting up analysis files...')

    includes = args.includes + [os.path.join(root_dir, 'lib')]
    harness = os.path.join(args.output_dir, 'harness.c')
    if preprocess_file(args.file, harness, includes, args.boolops) != 0:
        log.error(f'Failed to process input file \'{args.file}\'!')
        return -1

    configure(args.output_dir, root_dir, args.source, args.includes)

    if compile_sources(args.output_dir) != 0:
        log.error(f'Failed to compile project sources!')
        return -1

    wasm_harness = os.path.splitext(harness)[0] + '.wat'
    if postprocess_file(wasm_harness) != 0:
        log.error(f'Failed to annotate Wasm module!')
        return -1

    # run WASP
    analyser = WASP()
    #analyser = exe.WASP(instr_limit=10000000,time_limit=20)
    log.info('Starting WASP...')
    res = analyser.run(wasm_harness, args.output_dir)
    with open(wasm_harness + '.out', 'w') as out, \
            open(wasm_harness + '.err', 'w') as err:
        out.write(res.stdout)
        err.write(res.stderr)
    if res.crashed:
        log.error(f'WASP crashed')
        return -1
    elif res.timeout:
        log.error(f'WASP timed out')
        return -1
    log.info('Analysis done.')
    return 0
