#!/usr/bin/env python3
import os, sys, subprocess, json

def main():
    error_names = []

    print("Running failingING tests.....")
    # failinging tests
    for file in sorted(filter(lambda f : f.endswith('.wast'), \
            os.listdir('tests/failing'))):
        print('Running tests/failing/' + file, end='... ')
        sys.stdout.flush()
        try:
            out = subprocess.check_output(['./wasp', 'tests/failing/' + file], \
                    stderr=subprocess.STDOUT)
            report = json.loads(out)
            if not report['specification']:
                print('OK')
            else:
                print('NOK')
                error_names.append('tests/failing/' + file)
        except subprocess.CalledProcessError as e:
            print('NOK')
            error_names.append('tests/failing/' + file)

    print("\nRunning passingING tests.....")
    # failinging tests
    for file in sorted(filter(lambda f : f.endswith('.wast'), \
            os.listdir('tests/passing'))):
        print('Running tests/passing/' + file, end='... ')
        sys.stdout.flush()
        try:
            out = subprocess.check_output(['./wasp', 'tests/passing/' + file], \
                    stderr=subprocess.STDOUT)
            report = json.loads(out)
            if report['specification']:
                print('OK')
            else:
                print('NOK')
                error_names.append("tests/passing/" + file)
        except subprocess.CalledProcessError as e:
            print('NOK')
            error_names.append("tests/passing/" + file)

    print("Tests that are not behaving correctly: " + \
            str(error_names) + ".\n")

main()
