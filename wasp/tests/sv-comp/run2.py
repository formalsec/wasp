#!/usr/bin/env python3
import glob, yaml, csv, subprocess
import sys, threading, logging, time, resource

# Timeout (in seconds)
# Default SV-COMP is 15Mins
TIMEOUT = 900

# Maximum instructions executed in model
# This is the default setting
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
            #f'{ROOT_DIR}/ntdrivers',),
            (f'{ROOT_DIR}/ntdrivers-simplified', 'unreach-call'),
            (f'{ROOT_DIR}/openssl', 'unreach-call'),
            (f'{ROOT_DIR}/openssl-simplified', 'unreach-call'),
            (f'{ROOT_DIR}/locks', 'unreach-call')
            ],
        'floats' : [
            (f'{ROOT_DIR}/float-benchs', 'unreach-call'),
            (f'{ROOT_DIR}/float-newlib', 'unreach-call'),
            (f'{ROOT_DIR}/floats-cbmc-regression', 'unreach-call'),
            (f'{ROOT_DIR}/floats-cdfpl', 'unreach-call'),
            (f'{ROOT_DIR}/floats-esbmc-regression', 'unreach-call'),
            (f'{ROOT_DIR}/loop-floats-scientific-comp', 'unreach-call')
            ],
        'heap' : [
            (f'{ROOT_DIR}/forester-heap', 'unreach-call'),
            (f'{ROOT_DIR}/heap-data', 'unreach-call'),
            (f'{ROOT_DIR}/list-ext-properties', 'unreach-call'),
            (f'{ROOT_DIR}/list-ext2-properties', 'unreach-call'),
            (f'{ROOT_DIR}/list-ext3-properties', 'unreach-call'),
            (f'{ROOT_DIR}/list-properties', 'unreach-call'),
            (f'{ROOT_DIR}/list-simple', 'unreach-call')
            ],
        'loops' : [
            (f'{ROOT_DIR}/loop-crafted', 'unreach-call'),
            (f'{ROOT_DIR}/loop-industry-pattern', 'unreach-call'),
            (f'{ROOT_DIR}/loop-invariants', 'unreach-call'),
            (f'{ROOT_DIR}/loop-invgen', 'unreach-call'),
            (f'{ROOT_DIR}/loop-lit', 'unreach-call'),
            (f'{ROOT_DIR}/loop-new', 'unreach-call'),
            (f'{ROOT_DIR}/loop-simple', 'unreach-call'),
            (f'{ROOT_DIR}/loop-zilu', 'no-overflow'),
            #f'{ROOT_DIR}/loops',),
            #f'{ROOT_DIR}/loops-crafted-1'),
            (f'{ROOT_DIR}/verifythis', 'unreach-call'),
            (f'{ROOT_DIR}/nla-digbench', 'no-overflow'),
            (f'{ROOT_DIR}/nla-digbench-scaling', 'unreach-call')
            ],
        'recursive' : [
            (f'{ROOT_DIR}/recursive', 'unreach-call'),
            (f'{ROOT_DIR}/recursive-simple', 'unreach-call'),
            (f'{ROOT_DIR}/recursive-with-pointer', 'unreach-call')
            ],
        'array_memsafety' : [
            (f'{ROOT_DIR}/array-memsafety', 'valid-memsafety'),
            (f'{ROOT_DIR}/array-memsafety-realloc', 'valid-memsafety')
            ],
        'heap_memsafety' : [
            (f'{ROOT_DIR}/memsafety', 'valid-memsafety'),
            (f'{ROOT_DIR}/memsafety-bftpd', 'valid-memsafety'),
            (f'{ROOT_DIR}/memsafety-ext', 'valid-memsafety'),
            (f'{ROOT_DIR}/memsafety-ext2', 'valid-memsafety'),
            ],
        'termination_controlflow' : [
            (f'{ROOT_DIR}/termination-crafted', 'unreach-call'),
            (f'{ROOT_DIR}/termination-crafted-lit', 'unreach-call'),
            (f'{ROOT_DIR}/termination-numeric', 'termination'), 
            (f'{ROOT_DIR}/reducercommutativity', 'unreach-call')
            ],
        #'sequentialized' : [(f'{ROOT_DIR}/systemc', 'unreach-call')],
        'xcsp'           : [(f'{ROOT_DIR}/xcsp', 'unreach-call')],
        'combinations'   : [(f'{ROOT_DIR}/combinations', 'unreach-call')],
        'eca'            : [(f'{ROOT_DIR}/psyco', 'unreach-call')]
}

def limit_virtual_memory():
    # SV-COMP 15GiB Limit
    limit = 15 * 1024 * 1024 * 1024
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))

def run(i : int):
    global results
    global timeout
    global instr_max
    global nthreads
    global lock
    global srcs
    global prop

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

        for p in data['properties']:
            if prop in p['property_file']:
                unreach = p['expected_verdict']
                break
        try:
            cmd = ['./wasp', test, '-e', \
                   '(invoke \"__original_main\")', \
                   '-m', str(instr_max)]
            t0 = time.time()
            out = subprocess.check_output(cmd, timeout=timeout, \
                    stderr=subprocess.STDOUT, preexec_fn=limit_virtual_memory)
            if 'INCOMPLETE' not in out.decode('utf-8'):
                complete = True
            ret = 'OK' if unreach else 'NOK'
        except (subprocess.TimeoutExpired, KeyboardInterrupt) as e:
            ret = 'TIMEOUT'
        except subprocess.CalledProcessError as e:
            output = e.stdout.decode('utf-8').lower() if e.stdout is not None else ''
            if 'out of memory' in output:
                ret = 'RLIMIT'
            else:
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
    global prop

    lock = threading.Lock()

    for key, value in tests.items():
        if key in ignore:
            continue

        for data in value:
            dir, prop = data[0], data[1]
            srcs = glob.glob('tests/sv-comp/' + dir + '/*.wat')

            threads = list()

            for i in range(nthreads):
                t = threading.Thread(target=run, args=(i,))
                threads.append(t)
                t.start()

            for t in threads:
                t.join()

        basename = key + '_t' + str(timeout) + '_im' + str(instr_max)
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
