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
        'Arrays' : [
            (f'{root_dir}/array-examples/*'         , 'coverage-error-call'),
            (f'{root_dir}/array-industry-pattern/*' , 'coverage-error-call'),
            (f'{root_dir}/reducercommutativity/*'   , 'coverage-error-call'),
            (f'{root_dir}/array-tiling/*'           , 'coverage-error-call'),
            (f'{root_dir}/array-programs/*'         , 'coverage-error-call'),
            (f'{root_dir}/array-crafted/*'          , 'coverage-error-call'),
            (f'{root_dir}/array-multidimensional/*' , 'coverage-error-call'),
            (f'{root_dir}/array-patterns/*'         , 'coverage-error-call'),
            (f'{root_dir}/array-cav19/*'            , 'coverage-error-call'),
            (f'{root_dir}/array-lopstr16/*'         , 'coverage-error-call'),
            (f'{root_dir}/array-fpi/*'              , 'coverage-error-call')
            ],
        'BitVectors' : [
            (f'{root_dir}/bitvector/*'              , 'coverage-error-call'),
            (f'{root_dir}/bitvector-regression/*'   , 'coverage-error-call'),
            (f'{root_dir}/bitvector-loops/*'        , 'coverage-error-call')
            ],
        'ControlFlow' : [
            (f'{root_dir}/ntdrivers-simplified/*'   , 'coverage-error-call'),
            (f'{root_dir}/openssl-simplified/*'     , 'coverage-error-call'),
            (f'{root_dir}/locks/*'                  , 'coverage-error-call'),
            #(f'{root_dir}/ntdrivers/*'              , 'coverage-error-call'),
            (f'{root_dir}/openssl/*'                , 'coverage-error-call')
            ],
        'Floats' : [
            (f'{root_dir}/floats-cdfpl/*'               , 'coverage-error-call'),
            (f'{root_dir}/floats-cbmc-regression/*'     , 'coverage-error-call'),
            (f'{root_dir}/float-benchs/*'               , 'coverage-error-call'),
            (f'{root_dir}/floats-esbmc-regression/*'    , 'coverage-error-call'),
            (f'{root_dir}/float-newlib/*'               , 'coverage-error-call'),
            (f'{root_dir}/loop-floats-scientific-comp/*', 'coverage-error-call')
            ],
        'Heap' : [
            (f'{root_dir}/heap-manipulation/*'      , 'coverage-error-call'),
            (f'{root_dir}/list-properties/*'        , 'coverage-error-call'),
            (f'{root_dir}/ldv-regression/*'         , 'coverage-error-call'),
            #(f'{root_dir}/ddv-machzwd/*'            , 'coverage-error-call'),
            (f'{root_dir}/forester-heap/*'          , 'coverage-error-call'),
            (f'{root_dir}/list-ext-properties/*'    , 'coverage-error-call'),
            (f'{root_dir}/list-ext2-properties/*'   , 'coverage-error-call'),
            (f'{root_dir}/ldv-sets/*'               , 'coverage-error-call'),
            (f'{root_dir}/list-simple/*'            , 'coverage-error-call'),
            (f'{root_dir}/heap-data/*'              , 'coverage-error-call'),
            (f'{root_dir}/list-ext3-properties/*'   , 'coverage-error-call')
            ],
        'Loops' : [
            (f'{root_dir}/loops/*'                  , 'coverage-error-call'),
            (f'{root_dir}/loop-acceleration/*'      , 'coverage-error-call'),
            (f'{root_dir}/loop-crafted/*'           , 'coverage-error-call'),
            (f'{root_dir}/loop-invgen/*'            , 'coverage-error-call'),
            (f'{root_dir}/loop-lit/*'               , 'coverage-error-call'),
            (f'{root_dir}/loop-new/*'               , 'coverage-error-call'),
            (f'{root_dir}/loop-industry-pattern/*'  , 'coverage-error-call'),
            (f'{root_dir}/loops-crafted-1/*'        , 'coverage-error-call'),
            (f'{root_dir}/loop-invariants/*'        , 'coverage-error-call'),
            (f'{root_dir}/loop-simple/*'            , 'coverage-error-call'),
            (f'{root_dir}/loop-zilu/*'              , 'no-overflow'),
            (f'{root_dir}/verifythis/duplets'       , 'coverage-error-call'),
            (f'{root_dir}/verifythis/elimination_max', 'coverage-error-call'),
            (f'{root_dir}/verifythis/lcp'           , 'coverage-error-call'),
            (f'{root_dir}/verifythis/prefixsum_iter', 'coverage-error-call'),
            (f'{root_dir}/verifythis/tree_del_iter' , 'coverage-error-call'),
            (f'{root_dir}/verifythis/tree_del_iter_incorrect', 'coverage-error-call'),
            (f'{root_dir}/nla-digbench/*'           , 'coverage-error-call'),
            (f'{root_dir}/nla-digbench-scaling/*'   , 'coverage-error-call')
            ],
        'Recursive' : [
            (f'{root_dir}/recursive/*'              , 'coverage-error-call'),
            (f'{root_dir}/recursive-simple/*'       , 'coverage-error-call'),
            (f'{root_dir}/recursive-with-pointer/*' , 'coverage-error-call'),
            (f'{root_dir}/verifythis/prefixsum_rec' , 'coverage-error-call'),
            (f'{root_dir}/verifythis/tree_del_rec'  , 'coverage-error-call'),
            (f'{root_dir}/verifythis/tree_del_rec_incorrect', 'coverage-error-call'),
            (f'{root_dir}/verifythis/tree_max'      , 'coverage-error-call'),
            (f'{root_dir}/verifythis/tree_max_incorrect', 'coverage-error-call'),
            (f'{root_dir}/verifythis/elimination_max_rec', 'coverage-error-call'),
            (f'{root_dir}/verifythis/elimination_max_rec_onepoint', 'coverage-error-call'),
            ],
        'Sequentialized' : [(f'{root_dir}/systemc/*', 'coverage-error-call')],
        'XCSP'           : [(f'{root_dir}/xcsp/*'   , 'coverage-error-call')],
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

    while True:
        verdict  = True
        complete = True

        try:
            lock.acquire()
            data = srcs.pop()
        except IndexError:
            break
        finally:
            lock.release()

        test, prop = data[0], data[1]

        yml = test.replace('.wat', '.yml')
        with open(yml, 'r') as f:
            data = yaml.safe_load(f)

        for p in data['properties']:
            if prop in p['property_file']:
                verdict = False
                break
        else:
            continue

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

    srcs = []
    for tup in val:
        bm, prop = tup[0], tup[1]
        srcs = srcs + list(map(lambda t: (t, prop), glob.glob(f'tests/sv-benchmarks/{bm}.wat')))

    threads = []
    for i in range(num_threads):
        t = threading.Thread(target=run, args=(i,))
        threads.append(t)
        t.start()

    for t in threads:
        t.join()

    tbl_name = f'{key}_t{timeout}_im{instruction_max}'
    with open(f'tests/sv-benchmarks/results/{tbl_name}.csv', 'w', \
            newline='') as f:
        writer = csv.writer(f)
        writer.writerows(results)
#-----------------------------------------------------------
