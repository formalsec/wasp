#!/usr/bin/env python
from functools import reduce
import os, sys, argparse, subprocess, time

def getDirEntry(basename : str):
        lst = list(map(lambda f : f.name, \
                filter(lambda e : e.name.endswith(('.wat', '.wast')), \
                os.scandir(basename))))
        return dict(dirPath=basename, testLst=lst, \
                size=len(lst), okCnt=0, errorLst=list(), totalTime=0)

def runTestsInDir(dirEntry : dict):
    print('Entering ' + dirEntry['dirPath'])

    for testName in dirEntry['testLst']:
        testPath = dirEntry['dirPath'] + testName
        print('Running ' + testPath, end='... ')
        sys.stdout.flush()
        try:
            cmd = ['./wasp', testPath, '-e', \
                    '(invoke \"__original_main\")']
            t0 = time.time()
            subprocess.check_output(cmd, timeout=10, stderr=subprocess.STDOUT)
            t1 = time.time()
            dirEntry['okCnt'] += 1
            dirEntry['totalTime'] += t1-t0
            print(f'OK (time={t1-t0}s)')
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as e:
            print('NOK')
            dirEntry['errorLst'].append(testPath)

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
    else:
        print('Running Normal GillianBenchmarks...')
        runBenchmarks('tests/collections-c/_build/for-wasp/normal/')
        print('Running Bug GillianBenchmarks...')
        runTestsInDir(getDirEntry('tests/collections-c/_build/for-wasp/bugs/'))
