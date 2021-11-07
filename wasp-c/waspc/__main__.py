import sys

from waspc import logger as logging
from waspc import visitor as pre

def preprocess_file(inFile, outFile):
    logging.debug('Starting pre-processor...')
    # logging.debug('Using arguments blah') 
    harness = pre.process(inFile)
    with open(outFile, 'w') as out:
        out.write(harness)

def compile_file(filename):
    logging.debug('Compiling...')
    llvm_ir = filename.replace('.c', '.bc')
    object = filename.replace('.c', '.o')
    wasm = filename.replace('.c', '.wasm')

def postprocess_file(inFile):
    logging.debug('Starting post-processor...')
    pass

def main(inFile):

    logging.init(logging.DEBUG) 
    outFile = 'harness.c'

    preprocess_file(inFile, outFile)
    compile_file(outFile)
    postprocess_file(outFile.replace('.c', '.wasm'))

    # run WASP

if __name__ == '__main__':
    main(sys.argv[1])
