# WASP-C

## Requirements

This package of WASP-C was tested on Ubuntu 20.04.5 LTS. We assume that the 
following software is available in the underlying system:

1. gcc version 9.4.0 
2. GNU Make 4.2.1
3. Python 3.8.10:
  1. lxml 4.9.1
4. GLIBC 2.31

## Running

You can call the executable with the following arguments:

```sh
usage: wasp-c [-h] [--version] [--output OUTPUT_DIR] [--include INCLUDES] [--source SOURCE] [--verbose] [--rm-boolops] [--entry ENTRY_FUNC] [--smt-assume] [--no-simplify] [--policy POLICY] [--queries]
              [--test-comp] [--property PROPERTY]
              file
```

where:

```
positional arguments:
  file                  file to analyse

options:
  -h, --help            show this help message and exit
  --version, -v         show program's version number and exit
  --output OUTPUT_DIR, -o OUTPUT_DIR
                        output directory to write to (default: output)
  --include INCLUDES, -I INCLUDES
                        include headers path (default: [])
  --source SOURCE, -S SOURCE
                        lib source code (default: )
  --verbose             show messages verbose (default: False)
  --rm-boolops          remove short-circuit evaluation (default: False)
  --entry ENTRY_FUNC    entry function to start analysis (default: __original_main)
  --smt-assume          use the solver to progress in the assume rule (default: False)
  --no-simplify         do not perform algebraic simplifications of symbolic expressions (default: False)
  --policy POLICY       search policy: random|depth|breadth (default: random)
  --queries             output solver queries in .smt2 format (default: False)
  --test-comp           test-comp instrumentation and xml test suite (default: False)
  --property PROPERTY, -p PROPERTY
                        property file (default: None)
```

A sample Test-Comp run command is as follows:

```sh
./bin/wasp-c --smt-assume --policy breadth --test-comp --property properties/coverage-error-call.prp examples/CostasArray-10.c
```
