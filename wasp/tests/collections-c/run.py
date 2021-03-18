#!/usr/bin/env python
from functools import reduce
import os, sys, argparse, subprocess

def getDirEntry(basename : str):
        lst = list(map(lambda f : f.name, \
                filter(lambda e : e.name.endswith(('.wat', '.wast')), \
                os.scandir(basename))))
        return dict(dirPath=basename, testLst=lst, \
                size=len(lst), okCnt=0, errorLst=list())

def runTestsInDir(dirEntry : dict):
    print('Entering ' + dirEntry['dirPath'])

    for testName in dirEntry['testLst']:
        testPath = dirEntry['dirPath'] + testName
        print('Running ' + testPath, end='... ')
        sys.stdout.flush()
        try:
            cmd = ['./wasp', testPath, '-e', \
                    '(invoke \"__original_main\")']
            subprocess.check_output(cmd, timeout=5, stderr=subprocess.STDOUT)
            dirEntry['okCnt'] += 1
            print('OK')
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as e:
            print('NOK')
            dirEntry['errorLst'].append(testPath)

    print('\nRESULTS: {}/{}'.format(dirEntry['okCnt'], \
            dirEntry['size']))
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
    print('FINAL RESULTS: {}/{} OKs'.format(c, t))

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('dir', nargs='?')
    args = parser.parse_args()

    if args.dir is not None:
        print('Running tests in \'{}\'...'.format(args.dir))
        print('-' * 0x41)
        runTestsInDir(getDirEntry(args.dir + '/'))
    else:
        print('Running GillianBenchmarks...')
        runBenchmarks('tests/collections-c/_build/for-wasp/normal/')
