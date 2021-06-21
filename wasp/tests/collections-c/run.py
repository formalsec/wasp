#!/usr/bin/env python3
import glob, sys, time, json, subprocess, os, csv, logging

# globals --------------------------------------------------
timeout=20
instruction_max=10000000
dirs = glob.glob('tests/collections-c/_build/for-wasp/normal/*')
table = [['category', 'tests', 'paths', 'time']]
errors = list()
#-----------------------------------------------------------

# helpers --------------------------------------------------
cmd  = lambda p : ['./wasp', p, '-e', '(invoke \"__original_main\")', \
                   '-m', str(instruction_max)]
def run(test : str):
    try:
        out = subprocess.check_output(cmd(test), timeout=timeout, \
                stderr=subprocess.STDOUT)
    except (subprocess.CalledProcessError, \
            subprocess.TimeoutExpired) as e:
        return None
    return out
#-----------------------------------------------------------

# main -----------------------------------------------------
fmt = '%(asctime)s: %(message)s'
date_fmt = '%H:%M:%S'
logging.basicConfig(format=fmt, level=logging.INFO, \
        datefmt=date_fmt)

for dir in dirs:
    sum_paths, sum_time = 0, 0.0
    tests = glob.glob(f'{dir}/*.wat')
    for test in tests:
        t0    = time.time()
        out   = run(test)
        delta = time.time() - t0
        
        # Oh no! we crashed!!
        if out is None:
            errors.append(test)
            logging.info('Crashed {os.path.basename(test)}')
            continue

        report = json.loads(out)
        if not report['specification']:
            errors.append(test)

        sum_time += delta
        sum_paths += report['paths_explored']

        logging.info(f'Test {os.path.basename(test)} ' \
              f'({"OK" if report["specification"] else "NOK"}, ' \
              f'{round(delta,2)}s, {report["instruction_counter"]})')

    table.append([f'{os.path.basename(dir)}', len(tests), \
            int(sum_paths/len(tests)), round(sum_time, 2)])

with open('tests/collections-c/table.csv', 'w', newline='') as f:
    writer = csv.writer(f)
    writer.writerows(table)

for err in errors:
    logging.info('Failed Test: ' + err)
#-----------------------------------------------------------
