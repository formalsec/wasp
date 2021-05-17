#!/usr/bin/env python
from functools import reduce
import os, sys, argparse, subprocess, time, yaml, csv

csv_report = [['name', 'ans', 'verdict', 'complete', 'time', 'timeout', 'crash']]

def getDirEntry(basename : str):
        lst = list(map(lambda f : f.name, \
                filter(lambda e : e.name.endswith(('.wat', '.wast')), \
                os.scandir(basename))))
        return dict(dirPath=basename, testLst=lst, \
                size=len(lst), okCnt=0, errorLst=list(), totalTime=0)

def runTestsInDir(dirEntry : dict):
    print('Entering ' + dirEntry['dirPath'])

    ret = ''
    for testName in dirEntry['testLst']:
        ret      = ''
        crash    = False
        timeout  = False
        complete = False
        unreach  = True

        testPath = dirEntry['dirPath'] + testName
        print('Running ' + testPath, end='... ')
        sys.stdout.flush()
        yml = testPath.replace('.wat', '.yml')
        with open(yml, 'r') as y:
            data = yaml.safe_load(y)
            for prop in data['properties']:
                if 'unreach-call' in prop['property_file']:
                    unreach = prop['expected_verdict']
                elif 'valid-memsafety' in prop['property_file']:
                    unreach = prop['expected_verdict']
        try:
            cmd = ['./wasp', testPath, '-e', \
                    '(invoke \"__original_main\")', \
                    '-m', '1000000']
            t0 = time.time()
            out = subprocess.check_output(cmd, timeout=10, stderr=subprocess.STDOUT)
            if 'INCOMPLETE' not in out.decode('utf-8'):
                complete = True
            if unreach:
                ret = 'OK'
                dirEntry['okCnt'] += 1
            else:
                ret = 'NOK'
                dirEntry['errorLst'].append(testPath)
        except subprocess.CalledProcessError  as e:
            if unreach:
                ret = 'CRASH'
                crash = True
                dirEntry['errorLst'].append(testPath)
            else:
                ret = 'OK'
                dirEntry['okCnt'] += 1
        except (subprocess.TimeoutExpired, KeyboardInterrupt) as e:
            ret = 'TIMEOUT'
            timeout = True
            dirEntry['errorLst'].append(testPath)
        finally:
            verdict = 'OK' if unreach else 'NOK'
            t1 = time.time()
            interval = t1-t0
            dirEntry['totalTime'] += interval
            print(f'{ret} (time={t1-t0}s)')
            csv_report.append([testPath, ret, verdict, complete, interval, timeout, crash])



    print(f"\nRESULTS: {dirEntry['okCnt']}/{dirEntry['size']} " \
          f"(total={dirEntry['totalTime']}, " \
          f"avg={dirEntry['totalTime']/dirEntry['size']})")
    if len(dirEntry['errorLst']):
        print('TESTS NOT OK:')
        list(map(lambda t : print(t), dirEntry['errorLst']))

def runBenchmarks(basename : str):

    tests = list(getDirEntry(basename + d.name + '/') for d in \
            filter(lambda e : e.is_dir(), os.scandir(basename)))

    for dirEntry in tests:
        print('-' * 0x41)
        runTestsInDir(dirEntry)

    print('-' * 0x41, end='\n\n')
    t = reduce(lambda a, b: a + b, map(lambda d : d['size'],  \
            tests))
    c = reduce(lambda a, b: a + b, map(lambda d : d['okCnt'], \
            tests))
    time = reduce (lambda a, b: a + b, map(lambda d : d['totalTime'], \
            tests))
    avg = time / t
    print(f'FINAL RESULTS: {c}/{t} OKs\n total={time}, avg={avg}')

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('dir', nargs='?')
    args = parser.parse_args()

    if args.dir is not None:
        print('Running tests in \'{}\'...'.format(args.dir))
        print('-' * 0x41)
        runTestsInDir(getDirEntry(args.dir + '/'))

        with open("tests/sv-comp/report.csv", "a", newline="") as f:
            writer = csv.writer(f)
            writer.writerows(csv_report)
    else:
        print('Running SV-COMP...')
        runBenchmarks('tests/sv-comp/_build/')

        with open("tests/sv-comp/report.csv", "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerows(csv_report)
