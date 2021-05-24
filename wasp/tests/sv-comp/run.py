#!/usr/bin/env python
from functools import reduce
import os, sys, argparse, subprocess, time, yaml, csv

# DEFAULTS
TIMEOUT=10
INSTR_MAX=1000000

csv = [['name', 'ans', 'verdict', 'complete', 'time']]

array = [
        'for-wasp/array-cav19', 
        'for-wasp/array-crafted', 
        'for-wasp/array-examples',
        'for-wasp/array-fpi',
        'for-wasp/array-industry-pattern',
        'for-wasp/array-lopstr16',
        'for-wasp/array-multidimensional',
        'for-wasp/array-patterns',
        'for-wasp/array-programs',
        'for-wasp/array-tiling'
]

bitvector = [
        'for-wasp/bitvector',
        'for-wasp/bitvector-loops',
        'for-wasp/bitvector-regression'
]

control_flow = [
        #'for-wasp/ntdrivers',
        'for-wasp/ntdrivers-simplified',
        'for-wasp/openssl',
        'for-wasp/openssl-simplified',
        'for-wasp/locks'
]

eca = ['for-wasp/psyco']

floats = [
        'for-wasp/float-benchs',
        'for-wasp/float-newlib',
        'for-wasp/floats-cbmc-regression',
        'for-wasp/floats-cdfpl',
        'for-wasp/floats-esbmc-regression',
        'for-wasp/loop-floats-scientific-comp'
]

heap = [
        'for-wasp/forester-heap',
        'for-wasp/heap-data',
        'for-wasp/list-ext-properties',
        'for-wasp/list-ext2-properties',
        'for-wasp/list-ext3-properties',
        'for-wasp/list-properties',
        'for-wasp/list-simple'
]

loops = [
        'for-wasp/loop-crafted',
        'for-wasp/loop-industry-pattern',
        'for-wasp/loop-invariants',
        'for-wasp/loop-invgen',
        'for-wasp/loop-lit',
        'for-wasp/loop-new',
        'for-wasp/loop-simple',
        'for-wasp/loop-zilu',
        #'for-wasp/loops',
        #'for-wasp/loops-crafted-1'
        'for-wasp/verifythis',
        'for-wasp/nla-digbench',
        'for-wasp/nla-digbench-scaling'
]

recursive = [
        'for-wasp/recursive',
        'for-wasp/recursive-simple',
        'for-wasp/recursive-with-pointer'
]

sequentialized = ['for-wasp/systemc']

xcsp = ['for-wasp/xcsp']

combinations = ['for-wasp/combinations']

array_memsafety = [
        'for-wasp/array-memsafety',
        'for-wasp/array-memsafety-realloc'
]

heap_memsafety = [
        'for-wasp/memsafety',
        'for-wasp/memsafety-bftpd',
        'for-wasp/memsafety-ext',
        'for-wasp/memsafety-ext2'
]

termination_controlflow = [
        'for-wasp/termination-crafted',
        'for-wasp/termination-crafted-lit',
        'for-wasp/termination-numeric',
        'for-wasp/reducercommutativity'
]

test_dict = {
        'array' : array,
        'bitvector' : bitvector,
        'control_flow' : control_flow,
        'eca' : eca,
        'floats' : floats,
        'heap' : heap,
        'loops' : loops,
        'recursive' : recursive, 
        'sequentialized' : sequentialized,
        'XCSP' : xcsp,
        'combinations' : combinations,
        'array-memsafety' : array_memsafety,
        'heap-memsafety' : heap_memsafety,
        'termination-controlflow' : termination_controlflow
}

def getDirEntry(basename : str):
        lst = list(map(lambda f : f.name, \
                filter(lambda e : e.name.endswith(('.wat', '.wast')), \
                os.scandir(basename))))
        return dict(dirPath=basename, testLst=lst, \
                size=len(lst), okCnt=0, errorLst=list(), totalTime=0)

def runTestsInDir(dirEntry : dict, timeout, instr_max):
    print('Entering ' + dirEntry['dirPath'])

    ret = ''
    for testName in dirEntry['testLst']:
        ret      = ''
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
                    '-m', str(instr_max)]
            t0 = time.time()
            out = subprocess.check_output(cmd, timeout=timeout, stderr=subprocess.STDOUT)
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
                dirEntry['errorLst'].append(testPath)
            else:
                ret = 'OK'
                dirEntry['okCnt'] += 1
        except (subprocess.TimeoutExpired, KeyboardInterrupt) as e:
            ret = 'TIMEOUT'
            dirEntry['errorLst'].append(testPath)
        finally:
            verdict = 'OK' if unreach else 'NOK'
            t1 = time.time()
            interval = t1-t0
            dirEntry['totalTime'] += interval
            print(f'{ret} (time={t1-t0}s)')
            csv.append([testPath, ret, verdict, complete, interval])



    print(f"\nRESULTS: {dirEntry['okCnt']}/{dirEntry['size']} " \
          f"(total={dirEntry['totalTime']}, " \
          f"avg={dirEntry['totalTime']/dirEntry['size']})")
    if len(dirEntry['errorLst']):
        print('TESTS NOT OK:')
        list(map(lambda t : print(t), dirEntry['errorLst']))

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('timeout', nargs='?')
    parser.add_argument('instr_max', nargs='?')
    args = parser.parse_args()

    timeout   = args.timeout   if args.timeout   is not None else TIMEOUT
    instr_max = args.instr_max if args.instr_max is not None else INSTR_MAX

    for key, value in test_dict.items():
        list(map(
            lambda d: runTestsInDir(getDirEntry('tests/sv-comp/' + d + '/_build/'), \
                                    timeout, instr_max), \
            value))

        with open("tests/sv-comp/out/" + key + ".csv", "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerows(csv)

        csv = [['name', 'ans', 'verdict', 'complete', 'time']]
