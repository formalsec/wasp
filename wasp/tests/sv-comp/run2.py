#!/usr/bin/env python3
import glob, yaml, csv, subprocess
import sys, threading, logging, time

# Timeout (in seconds)
TIMEOUT = 10

# Maximum instructions executed in model
INSTR_MAX = 1000000

ignore = ['array', 'bitvector', 'control_flow']

tests = {
        'array' : [
            'for-wasp/array-cav19', 
            'for-wasp/array-crafted', 
            'for-wasp/array-examples',
            'for-wasp/array-fpi',
            'for-wasp/array-industry-pattern',
            'for-wasp/array-lopstr16',
            'for-wasp/array-multidimensional',
            'for-wasp/array-patterns',
            'for-wasp/array-programs',
            'for-wasp/array-tiling'
            ],
        'bitvector' : [
            'for-wasp/bitvector',
            'for-wasp/bitvector-loops',
            'for-wasp/bitvector-regression'
            ],
        'control_flow' : [
            #'for-wasp/ntdrivers',
            'for-wasp/ntdrivers-simplified',
            'for-wasp/openssl',
            'for-wasp/openssl-simplified',
            'for-wasp/locks'
            ],
        'floats' : [
            'for-wasp/float-benchs',
            'for-wasp/float-newlib',
            'for-wasp/floats-cbmc-regression',
            'for-wasp/floats-cdfpl',
            'for-wasp/floats-esbmc-regression',
            'for-wasp/loop-floats-scientific-comp'
            ],
        'heap' : [
            'for-wasp/forester-heap',
            'for-wasp/heap-data',
            'for-wasp/list-ext-properties',
            'for-wasp/list-ext2-properties',
            'for-wasp/list-ext3-properties',
            'for-wasp/list-properties',
            'for-wasp/list-simple'
            ],
        'loops' : [
            'for-wasp/loop-crafted',
            'for-wasp/loop-industry-pattern',
            'for-wasp/loop-invariants',
            'for-wasp/loop-invgen',
            'for-wasp/loop-lit',
            'for-wasp/loop-new',
            'for-wasp/loop-simple',
            'for-wasp/loop-zilu',
            #'for-wasp/loops',
            #'for-wasp/loops-crafted-1'
            'for-wasp/verifythis',
            'for-wasp/nla-digbench',
            'for-wasp/nla-digbench-scaling'
            ],
        'recursive' : [
            'for-wasp/recursive',
            'for-wasp/recursive-simple',
            'for-wasp/recursive-with-pointer'
            ],
        'array_memsafety' : [
            'for-wasp/array-memsafety',
            'for-wasp/array-memsafety-realloc'
            ],
        'heap_memsafety' : [
            'for-wasp/memsafety',
            'for-wasp/memsafety-bftpd',
            'for-wasp/memsafety-ext',
            'for-wasp/memsafety-ext2'
            ],
        'termination_controlflow' : [
            'for-wasp/termination-crafted',
            'for-wasp/termination-crafted-lit',
            'for-wasp/termination-numeric',
            'for-wasp/reducercommutativity'
            ],
        'sequentialized' : ['for-wasp/systemc'],
        'xcsp'           : ['for-wasp/xcsp'],
        'combinations'   : ['for-wasp/combinations'],
        'eca'            : ['for-wasp/psyco']
}

def run(i : int):
    global results
    global timeout
    global instr_max
    global nthreads
    global lock
    global srcs

    while True:
        complete = False
        unreach = True

        try:
            lock.acquire()
            test = srcs.pop()
            lock.release()
        except IndexError:
            lock.release()
            break

        yml = test.replace('.wat', '.yml')
        with open(yml, 'r') as f:
            data = yaml.safe_load(f)

        for prop in data['properties']:
            if 'unreach-call' in prop['property_file']:
                unreach = prop['expected_verdict']
                break
            elif 'valid_memsafety' in prop['property_file']:
                unreach = prop['expected_verdict']
                break
        try:
            cmd = ['./wasp', test, '-e', \
                   '(invoke \"__original_main\")', \
                   '-m', str(instr_max)]
            t0 = time.time()
            out = subprocess.check_output(cmd, timeout=timeout, stderr=subprocess.STDOUT)
            if 'INCOMPLETE' not in out.decode('utf-8'):
                complete = True
            ret = 'OK' if unreach else 'NOK'
        except (subprocess.TimeoutExpired, KeyboardInterrupt) as e:
            ret = 'TIMEOUT'
        except:
            ret = 'CRASH' if unreach else 'OK'
        finally:
            verdict = 'OK' if unreach else 'NOK'
            t1 = time.time()
            delta = t1-t0
            lock.acquire()
            results.append([test, ret, verdict, complete, delta])
            lock.release()
        logging.info(f'Thread={i} File=\'{test}\', Ret={ret}, T={delta}s')

def parse_arg(i : int) -> str:
    try:
        return sys.argv[i]
    except:
        return None

def main():
    global lock
    global results
    global srcs

    lock = threading.Lock()

    for key, value in tests.items():
        if key in ignore:
            continue

        for dir in value:
            srcs = glob.glob('tests/sv-comp/' + dir + '/_build/*.wat')

            threads = list()

            for i in range(nthreads):
                t = threading.Thread(target=run, args=(i,))
                threads.append(t)
                t.start()

            for t in threads:
                t.join()

        basename = key + '_' + str(timeout) + '_im' + str(instr_max)
        with open(f'tests/sv-comp/results/{basename}.csv', 'w', newline='') as f:
            writer = csv.writer(f)
            writer.writerows(results)

        results = [['name', 'ans', 'verdict', 'complete', 'time']]

if __name__ == '__main__':
    global results
    global timeout
    global instr_max
    global nthreads

    timeout   = int(parse_arg(1)) if parse_arg(1) is not None else TIMEOUT
    instr_max = int(parse_arg(2)) if parse_arg(2) is not None else INSTR_MAX
    nthreads  = int(parse_arg(3)) if parse_arg(3) is not None else 1
    results   = [['name', 'ans', 'verdict', 'complete', 'time']]

    format = "%(asctime)s: %(message)s"
    logging.basicConfig(format=format, level=logging.INFO, \
            datefmt="%H:%M:%S")

    logging.info(f'Starting sv-comp benchmarks...')
    logging.info(f'Using timeout={timeout}')
    logging.info(f'Using instr_max={instr_max}')
    logging.info(f'Using nthreads={nthreads}')

    main()
