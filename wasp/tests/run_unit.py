#!/usr/bin/env python
import os, sys, subprocess

def main():
    error_names = []

    print("Running FAILING tests.....")
    # Failing tests
    for file in sorted(filter(lambda f : f.endswith('.wast'), \
            os.listdir('tests/fail'))):
        print('Running tests/fail/' + file, end='... ')
        sys.stdout.flush()
        try:
            subprocess.check_output(['./wasp', 'tests/fail/' + file], \
                    stderr=subprocess.STDOUT)
            error_names.append('tests/fail/' + file)
            print('NOK')
        except subprocess.CalledProcessError as e:
            print('OK')

    print("\nRunning PASSING tests.....")
    # Failing tests
    for file in sorted(filter(lambda f : f.endswith('.wast'), \
            os.listdir('tests/pass'))):
        print('Running tests/pass/' + file, end='... ')
        sys.stdout.flush()
        try:
            subprocess.check_output(['./wasp', 'tests/pass/' + file], \
                    stderr=subprocess.STDOUT)
            print('OK')
        except subprocess.CalledProcessError as e:
            print('NOK')
            error_names.append("tests/pass/" + file)

    print("Tests that are not behaving correctly: " + \
            str(error_names) + ".\n")

main()
