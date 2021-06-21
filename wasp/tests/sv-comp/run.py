#!/usr/bin/env python3
import glob, yaml, csv, subprocess
import sys, threading, logging, time, resource, json

# globals --------------------------------------------------
# default SV-COMP is 15 mins
timeout = 900
instruction_max = 1000000
num_threads = 1
root_dir = '_build'
# populate with dirs to skip
ignore = []
tests = {
        'array' : [
            (f'{root_dir}/array-cav19', 'unreach-call'),
            (f'{root_dir}/array-crafted', 'unreach-call'),
            (f'{root_dir}/array-examples', 'unreach-call'),
            (f'{root_dir}/array-fpi', 'unreach-call'),
            (f'{root_dir}/array-industry-pattern', 'unreach-call'),
            (f'{root_dir}/array-lopstr16', 'unreach-call'),
            (f'{root_dir}/array-multidimensional', 'unreach-call'),
            (f'{root_dir}/array-patterns', 'unreach-call'),
            (f'{root_dir}/array-programs', 'unreach-call'),
            (f'{root_dir}/array-tiling', 'unreach-call')
            ],
        'bitvector' : [
            (f'{root_dir}/bitvector', 'unreach-call'),
            (f'{root_dir}/bitvector-loops', 'unreach-call'),
            (f'{root_dir}/bitvector-regression', 'unreach-call')
            ],
        'control_flow' : [
            #f'{root_dir}/ntdrivers',),
            (f'{root_dir}/ntdrivers-simplified', 'unreach-call'),
            (f'{root_dir}/openssl', 'unreach-call'),
            (f'{root_dir}/openssl-simplified', 'unreach-call'),
            (f'{root_dir}/locks', 'unreach-call')
            ],
        'floats' : [
            (f'{root_dir}/float-benchs', 'unreach-call'),
            (f'{root_dir}/float-newlib', 'unreach-call'),
            (f'{root_dir}/floats-cbmc-regression', 'unreach-call'),
            (f'{root_dir}/floats-cdfpl', 'unreach-call'),
            (f'{root_dir}/floats-esbmc-regression', 'unreach-call'),
            (f'{root_dir}/loop-floats-scientific-comp', 'unreach-call')
            ],
        'heap' : [
            (f'{root_dir}/forester-heap', 'unreach-call'),
            (f'{root_dir}/heap-data', 'unreach-call'),
            (f'{root_dir}/list-ext-properties', 'unreach-call'),
            (f'{root_dir}/list-ext2-properties', 'unreach-call'),
            (f'{root_dir}/list-ext3-properties', 'unreach-call'),
            (f'{root_dir}/list-properties', 'unreach-call'),
            (f'{root_dir}/list-simple', 'unreach-call')
            ],
        'loops' : [
            (f'{root_dir}/loop-crafted', 'unreach-call'),
            (f'{root_dir}/loop-industry-pattern', 'unreach-call'),
            (f'{root_dir}/loop-invariants', 'unreach-call'),
            (f'{root_dir}/loop-invgen', 'unreach-call'),
            (f'{root_dir}/loop-lit', 'unreach-call'),
            (f'{root_dir}/loop-new', 'unreach-call'),
            (f'{root_dir}/loop-simple', 'unreach-call'),
            (f'{root_dir}/loop-zilu', 'no-overflow'),
            #f'{root_dir}/loops',),
            #f'{root_dir}/loops-crafted-1'),
            (f'{root_dir}/verifythis', 'unreach-call'),
            (f'{root_dir}/nla-digbench', 'no-overflow'),
            (f'{root_dir}/nla-digbench-scaling', 'unreach-call')
            ],
        'recursive' : [
            (f'{root_dir}/recursive', 'unreach-call'),
            (f'{root_dir}/recursive-simple', 'unreach-call'),
            (f'{root_dir}/recursive-with-pointer', 'unreach-call')
            ],
        'array_memsafety' : [
            (f'{root_dir}/array-memsafety', 'valid-memsafety'),
            (f'{root_dir}/array-memsafety-realloc', 'valid-memsafety')
            ],
        'heap_memsafety' : [
            (f'{root_dir}/memsafety', 'valid-memsafety'),
            (f'{root_dir}/memsafety-bftpd', 'valid-memsafety'),
            (f'{root_dir}/memsafety-ext', 'valid-memsafety'),
            (f'{root_dir}/memsafety-ext2', 'valid-memsafety'),
            ],
        'termination_controlflow' : [
            (f'{root_dir}/termination-crafted', 'unreach-call'),
            (f'{root_dir}/termination-crafted-lit', 'unreach-call'),
            (f'{root_dir}/termination-numeric', 'termination'), 
            (f'{root_dir}/reducercommutativity', 'unreach-call')
            ],
        #'sequentialized' : [(f'{root_dir}/systemc', 'unreach-call')],
        'xcsp'           : [(f'{root_dir}/xcsp', 'unreach-call')],
        'combinations'   : [(f'{root_dir}/combinations', 'unreach-call')],
        'eca'            : [(f'{root_dir}/psyco', 'unreach-call')]
}
#-----------------------------------------------------------

# helpers --------------------------------------------------
cmd  = lambda p, i : ['./wasp', p, '-e', '(invoke \"__original_main\")', \
                   '-m', str(i)]

def get_arg(i : int) -> str:
    try:
        return sys.argv[i]
    except:
        return None

# Sets maximum virtual memory of a process
def limit_virtual_memory():
    # SV-COMP 15GiB Limit
    limit = 15 * 1024 * 1024 * 1024
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))

def run(i : int):
    global results
    global timeout
    global instruction_max 
    global num_threads 
    global lock
    global srcs
    global prop

    while True:
        verdict  = True
        complete = True

        try:
            lock.acquire()
            test = srcs.pop()
        except IndexError:
            break
        finally:
            lock.release()

        yml = test.replace('.wat', '.yml')
        with open(yml, 'r') as f:
            data = yaml.safe_load(f)

        for p in data['properties']:
            if prop in p['property_file']:
                verdict = p['expected_verdict']
                break

        t0 = time.time()
        try:
            out = subprocess.check_output(cmd(test, instruction_max), \
                    timeout=timeout, stderr=subprocess.STDOUT, \
                    preexec_fn=limit_virtual_memory)
            report = json.loads(out)
            complete = not report['incomplete']
            ret = str(report['specification'])
        except (subprocess.TimeoutExpired, KeyboardInterrupt) as e:
            ret = 'Timeout'
            complete = False
        except subprocess.CalledProcessError as e:
            ret = 'Crash'
            complete = False

        delta = round(time.time() - t0, 2)

        lock.acquire()
        results.append([test, ret, verdict, complete, delta])
        lock.release()

        logging.info(f'Thread={i} File=\'{test}\', Ret={ret}, T={delta}s')
#-----------------------------------------------------------

# main -----------------------------------------------------
fmt = '%(asctime)s: %(message)s'
date_fmt = '%H:%M:%S'
logging.basicConfig(format=fmt, level=logging.INFO, \
        datefmt=date_fmt)

arg1 = get_arg(1)
arg2 = get_arg(2)
arg3 = get_arg(3)
timeout         = int(arg1) if arg1 is not None else timeout
instruction_max = int(arg2) if arg2 is not None else instruction_max
num_threads     = int(arg3) if arg3 is not None else num_threads

logging.info(f'Starting SV-COMP benchmarks...')
logging.info(f'Using timeout={timeout}')
logging.info(f'Using instruction_max={instruction_max}')
logging.info(f'Using num_threads={num_threads}')

lock = threading.Lock()

for key, val in tests.items():
    results = [['test', 'answer', 'verdict', 'complete', 'time']]

    if key in ignore:
        continue

    for tup in val:
        dir, prop = tup[0], tup[1]
        srcs = glob.glob(f'tests/sv-comp/{dir}/*.wat')

        threads = []
        for i in range(num_threads):
            t = threading.Thread(target=run, args=(i,))
            threads.append(t)
            t.start()

        for t in threads:
            t.join()

    tbl_name = f'{key}_t{timeout}_im{instruction_max}'
    with open(f'tests/sv-comp/results/{tbl_name}.csv', 'w', \
            newline='') as f:
        writer = csv.writer(f)
        writer.writerows(results)
#-----------------------------------------------------------
