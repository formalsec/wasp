#!/usr/bin/env python3
import glob, sys, time, json, subprocess, os, csv

# defaults - you can experiment with these
TIMEOUT=20
INSTR_MAX=10000000

# don't change
CATS = glob.glob('tests/collections-c/_build/for-wasp/normal/*')
CMD  = lambda p : ['./wasp', p, '-e', '(invoke \"__original_main\")', \
                   '-m', str(INSTR_MAX)]
# stats
table = [['name', 'test_cnt', 'avg_paths', 'time']]
errors = list()

def run(test : str):
    total = 0
    runtime = 0
    iterations = 0

    print(f'Running {os.path.basename(test)}', end='... ')
    sys.stdout.flush()
    try:
        t0 = time.time()
        out = subprocess.check_output(CMD(test), timeout=TIMEOUT, \
                stderr=subprocess.STDOUT)
        t1 = time.time()
        report = json.loads(out)
        total = 1
        iterations = report['paths_explored']
        runtime = t1 - t0
        print(f'{"OK" if report["specification"] else "NOK"}'
              f' (time={t1-t0}s, lines={report["instruction_counter"]})')
        if not report['specification']:
            errors.append(test)
    except (subprocess.CalledProcessError, \
            subprocess.TimeoutExpired) as e:
        print('NOK')
        errors.append(test)
    return total, runtime, iterations

# main loop
for dir in CATS:
    total = 0
    total_time = 0.0
    iterations = 0
    for path in glob.glob(f'{dir}/*.wat'):
        t1, t2, t3 = run(path)
        total += t1
        total_time += t2
        iterations += t3
    # create report here
    table.append([f'{os.path.basename(dir)}', total, int(iterations/total), total_time])

with open('tests/collections-c/table.csv', 'w', newline='') as f:
    writer = csv.writer(f)
    writer.writerows(table)

print("Errors:")
print(errors)
