#!/usr/bin/env python3
from functools import reduce
import os, sys, argparse, subprocess, time, yaml, csv

# DEFAULTS
TIMEOUT=10
INSTR_MAX=1000000
ROOT_DIR='_build'

csv_lst = [['name', 'ans', 'verdict', 'complete', 'time']]

array = [
        f'{ROOT_DIR}/array-cav19', 
        f'{ROOT_DIR}/array-crafted', 
        f'{ROOT_DIR}/array-examples',
        f'{ROOT_DIR}/array-fpi',
        f'{ROOT_DIR}/array-industry-pattern',
        f'{ROOT_DIR}/array-lopstr16',
        f'{ROOT_DIR}/array-multidimensional',
        f'{ROOT_DIR}/array-patterns',
        f'{ROOT_DIR}/array-programs',
        f'{ROOT_DIR}/array-tiling'
]

bitvector = [
        f'{ROOT_DIR}/bitvector',
        f'{ROOT_DIR}/bitvector-loops',
        f'{ROOT_DIR}/bitvector-regression'
]

control_flow = [
        #f'{ROOT_DIR}/ntdrivers',
        f'{ROOT_DIR}/ntdrivers-simplified',
        f'{ROOT_DIR}/openssl',
        f'{ROOT_DIR}/openssl-simplified',
        f'{ROOT_DIR}/locks'
]

eca = [f'{ROOT_DIR}/psyco']

floats = [
        f'{ROOT_DIR}/float-benchs',
        f'{ROOT_DIR}/float-newlib',
        f'{ROOT_DIR}/floats-cbmc-regression',
        f'{ROOT_DIR}/floats-cdfpl',
        f'{ROOT_DIR}/floats-esbmc-regression',
        f'{ROOT_DIR}/loop-floats-scientific-comp'
]

heap = [
        f'{ROOT_DIR}/forester-heap',
        f'{ROOT_DIR}/heap-data',
        f'{ROOT_DIR}/list-ext-properties',
        f'{ROOT_DIR}/list-ext2-properties',
        f'{ROOT_DIR}/list-ext3-properties',
        f'{ROOT_DIR}/list-properties',
        f'{ROOT_DIR}/list-simple'
]

loops = [
        f'{ROOT_DIR}/loop-crafted',
        f'{ROOT_DIR}/loop-industry-pattern',
        f'{ROOT_DIR}/loop-invariants',
        f'{ROOT_DIR}/loop-invgen',
        f'{ROOT_DIR}/loop-lit',
        f'{ROOT_DIR}/loop-new',
        f'{ROOT_DIR}/loop-simple',
        f'{ROOT_DIR}/loop-zilu',
        #f'{ROOT_DIR}/loops',
        #f'{ROOT_DIR}/loops-crafted-1'
        f'{ROOT_DIR}/verifythis',
        f'{ROOT_DIR}/nla-digbench',
        f'{ROOT_DIR}/nla-digbench-scaling'
]

recursive = [
        f'{ROOT_DIR}/recursive',
        f'{ROOT_DIR}/recursive-simple',
        f'{ROOT_DIR}/recursive-with-pointer'
]

sequentialized = [f'{ROOT_DIR}/systemc']

xcsp = [f'{ROOT_DIR}/xcsp']

combinations = [f'{ROOT_DIR}/combinations']

array_memsafety = [
        f'{ROOT_DIR}/array-memsafety',
        f'{ROOT_DIR}/array-memsafety-realloc'
]

heap_memsafety = [
        f'{ROOT_DIR}/memsafety',
        f'{ROOT_DIR}/memsafety-bftpd',
        f'{ROOT_DIR}/memsafety-ext',
        f'{ROOT_DIR}/memsafety-ext2'
]

termination_controlflow = [
        f'{ROOT_DIR}/termination-crafted',
        f'{ROOT_DIR}/termination-crafted-lit',
        f'{ROOT_DIR}/termination-numeric',
        f'{ROOT_DIR}/reducercommutativity'
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
            csv_lst.append([testPath, ret, verdict, complete, interval])



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

    timeout   = int(args.timeout)   if args.timeout   is not None else TIMEOUT
    instr_max = int(args.instr_max) if args.instr_max is not None else INSTR_MAX

    for key, value in test_dict.items():
        list(map(
            lambda d: runTestsInDir(getDirEntry('tests/sv-comp/' + d), \
                                    timeout, instr_max), \
            value))

        fname = key + "_t" + str(timeout) + "_im" + str(instr_max)
        with open("tests/sv-comp/results/" + fname + ".csv", "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerows(csv_lst)

        csv_lst = [['name', 'ans', 'verdict', 'complete', 'time']]
