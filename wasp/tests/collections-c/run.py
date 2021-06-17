#!/usr/bin/env python3
import glob, sys, time, json, subprocess, os, csv, logging

#%%%%%%%%%%%%%%%%%%%%%%%%% DEFAULTS %%%%%%%%%%%%%%%%%%%%%%%%
# Experiment with these variables
# TIMEOUT: time we let WASP run
TIMEOUT=20
# INSTR_MAX: maximum instructions we let WASP execute
INSTR_MAX=10000000
#%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

#%%%%%%%%%%%%%%%%%%%%%%%%%% START %%%%%%%%%%%%%%%%%%%%%%%%%%
# Static globals
CATS = glob.glob('tests/collections-c/_build/for-wasp/normal/*')
# Globals
g_table = [['name', 'test_cnt', 'avg_paths', 'time']]
g_errors = list()

# Helpers
# cmd: command to execute test *p* in WASP
cmd  = lambda p : ['./wasp', p, '-e', '(invoke \"__original_main\")', \
                   '-m', str(INSTR_MAX)]
# Run 
def run(test : str):
    ret, ntime, paths = 0, 0, 0

    try:
        t0 = time.time()
        out = subprocess.check_output(cmd(test), timeout=TIMEOUT, \
                stderr=subprocess.STDOUT)
        t1 = time.time()
        report = json.loads(out)
        if not report['specification']:
            g_errors.append(test)

        ret, ntime, paths = 1, t1 - t0, report['paths_explored']
        logging.info( \
              f'Running {os.path.basename(test)}... ' \
              f'{"OK" if report["specification"] else "NOK"}' \
              f' (time={ntime}s, lines={report["instruction_counter"]})' \
        )
    except (subprocess.CalledProcessError, \
            subprocess.TimeoutExpired) as e:
        print('NOK')
        g_errors.append(test)
    return ret, ntime, paths

def main():
    # set up logger
    fmt = "%(asctime)s: %(message)s"
    logging.basicConfig(format=fmt, level=logging.INFO, \
            datefmt="%H:%M:%S")

    # main loop
    for dir in CATS:
        ntests, sum_time, sum_paths = 0, 0.0, 0

        for path in glob.glob(f'{dir}/*.wat'):
            ret, ntime, paths = run(path)
            ntests += ret
            sum_time += ntime
            sum_paths += paths

        g_table.append([f'{os.path.basename(dir)}', ntests, \
                int(sum_paths/ntests), sum_time])

    # write table to CSV file
    with open('tests/collections-c/table.csv', 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerows(g_table)

    # display failed tests
    for err in g_errors:
        logging.info('Failed Test: ' + err)

if __name__ == '__main__':
    main()
#%%%%%%%%%%%%%%%%%%%%%%%%%% END %%%%%%%%%%%%%%%%%%%%%%%%%%%%
