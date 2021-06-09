#!/usr/bin/env python3
import glob, yaml, csv, subprocess
import sys, threading, logging, time

# Timeout (in seconds)
TIMEOUT = 10

# Maximum instructions executed in model
INSTR_MAX = 1000000

# Dir where tests dir reside
ROOT_DIR = '_build'

# Populate with categories to ignore
ignore = []

# Testing categories
#   each category has a list of pairs (*dirPath*, *property*)
#   where, *dirPath* is the dir with tests and,
#          *property* is the property being tested

tests = {
        'array' : [
            (f'{ROOT_DIR}/array-cav19', 'unreach-call'),
            (f'{ROOT_DIR}/array-crafted', 'unreach-call'),
            (f'{ROOT_DIR}/array-examples', 'unreach-call'),
            (f'{ROOT_DIR}/array-fpi', 'unreach-call'),
            (f'{ROOT_DIR}/array-industry-pattern', 'unreach-call'),
            (f'{ROOT_DIR}/array-lopstr16', 'unreach-call'),
            (f'{ROOT_DIR}/array-multidimensional', 'unreach-call'),
            (f'{ROOT_DIR}/array-patterns', 'unreach-call'),
            (f'{ROOT_DIR}/array-programs', 'unreach-call'),
            (f'{ROOT_DIR}/array-tiling', 'unreach-call')
            ],
        'bitvector' : [
            (f'{ROOT_DIR}/bitvector', 'unreach-call'),
            (f'{ROOT_DIR}/bitvector-loops', 'unreach-call'),
            (f'{ROOT_DIR}/bitvector-regression', 'unreach-call')
            ],
        'control_flow' : [
            (#f'{ROOT_DIR}/ntdrivers',),
            (f'{ROOT_DIR}/ntdrivers-simplified', 'unreach-call'),
            (f'{ROOT_DIR}/openssl', 'unreach-call'),
            (f'{ROOT_DIR}/openssl-simplified', 'unreach-call'),
            (f'{ROOT_DIR}/locks', 'unreach-call')
            ],
        'floats' : [
            (f'{ROOT_DIR}/float-benchs',),
            (f'{ROOT_DIR}/float-newlib',),
            (f'{ROOT_DIR}/floats-cbmc-regression',),
            (f'{ROOT_DIR}/floats-cdfpl',),
            (f'{ROOT_DIR}/floats-esbmc-regression',),
            (f'{ROOT_DIR}/loop-floats-scientific-comp',)
            ],
        'heap' : [
            (f'{ROOT_DIR}/forester-heap',),
            (f'{ROOT_DIR}/heap-data',),
            (f'{ROOT_DIR}/list-ext-properties',),
            (f'{ROOT_DIR}/list-ext2-properties',),
            (f'{ROOT_DIR}/list-ext3-properties',),
            (f'{ROOT_DIR}/list-properties',),
            (f'{ROOT_DIR}/list-simple',)
            ],
        'loops' : [
            (f'{ROOT_DIR}/loop-crafted',),
            (f'{ROOT_DIR}/loop-industry-pattern',),
            (f'{ROOT_DIR}/loop-invariants',),
            (f'{ROOT_DIR}/loop-invgen',),
            (f'{ROOT_DIR}/loop-lit',),
            (f'{ROOT_DIR}/loop-new',),
            (f'{ROOT_DIR}/loop-simple',),
            (f'{ROOT_DIR}/loop-zilu',),
            (#f'{ROOT_DIR}/loops',),
            (#f'{ROOT_DIR}/loops-crafted-1'),
            (f'{ROOT_DIR}/verifythis',),
            (f'{ROOT_DIR}/nla-digbench',),
            (f'{ROOT_DIR}/nla-digbench-scaling',)
            ],
        'recursive' : [
            (f'{ROOT_DIR}/recursive',),
            (f'{ROOT_DIR}/recursive-simple',),
            (f'{ROOT_DIR}/recursive-with-pointer',)
            ],
        'array_memsafety' : [
            (f'{ROOT_DIR}/array-memsafety',),
            (f'{ROOT_DIR}/array-memsafety-realloc',)
            ],
        'heap_memsafety' : [
            (f'{ROOT_DIR}/memsafety',),
            (f'{ROOT_DIR}/memsafety-bftpd',),
            (f'{ROOT_DIR}/memsafety-ext',),
            (f'{ROOT_DIR}/memsafety-ext2',),
            ],
        'termination_controlflow' : [
            (f'{ROOT_DIR}/termination-crafted',),
            (f'{ROOT_DIR}/termination-crafted-lit',),
            (f'{ROOT_DIR}/termination-numeric',), 
            (f'{ROOT_DIR}/reducercommutativity', )
            ],
        'sequentialized' : [(f'{ROOT_DIR}/systemc', ),
        'xcsp'           : [(f'{ROOT_DIR}/xcsp', )],
        'combinations'   : [(f'{ROOT_DIR}/combinations', )],
        'eca'            : [(f'{ROOT_DIR}/psyco', )]
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
            srcs = glob.glob('tests/sv-comp/' + dir + '/*.wat')

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
