from __future__ import print_function
import os
import sys

from wasp import logger as logging
from wasp import visitor as pre

def preprocess_file(input_file, output_file):
    logging.debug('Starting pre-processor...')
    # logging.debug('Using arguments blah') 
    harness = pre.process(input_file)
    with open(output_file, 'w') as out:
        out.write(harness)

def compile_file(filename):
    logging.debug('Compiling...')
    llvm_ir = filename.replace('.c', '.bc')
    object = filename.replace('.c', '.o')
    wasm = filename.replace('.c', '.wasm')

def postprocess_file(inFile):
    logging.debug('Starting post-processor...')
    pass

def main(argv=None):

    if argv is None:
        argv = sys.argv

    if len(argv) != 3:
        print(f'usage: {argv[0]} <input_file> <output_path>')
        return -1

    logging.init(logging.DEBUG) 

    input_file = argv[1]
    output_dir = argv[2]

    if not os.path.exists(input_file):
        logging.error(f'File \'{input_file}\' not found.')
        return -1

    if not os.path.exists(output_dir):
        logging.debug(f'Creating directory \'{output_dir}\'.')
        os.makedirs(output_dir, exist_ok=True)

    output_file = os.path.join(output_dir, 'harness.c')
    preprocess_file(input_file, output_file)

    compile_file(output_file)
    postprocess_file(output_file.replace('.c', '.wasm'))

    # run WASP
    return 0
