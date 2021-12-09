# Concolic Execution for WebAssembly

Title of the submitted paper: Concolic Execution for WebAssembly
ECOOP submission number for the paper: 25

## Overview: What does the artifact comprise?

Please list for each distinct component of your artifact:

* The artificat is comprised of:
  * Code for the tools `WASP` and `WASP-C`
  * Three benchmark suites in C.
* The components of the artifact come in source code format 
  in the directory structure show [below](#layout)
* The artifact can be found in [Insert Link here](https://google.com)
* We claim the functional and available badges.

## For authors claiming a functional or reusable badge: What are claims about the artifact’s functionality to be evaluated by the committee?

* All the results from Table 2 and Table 3 can be obtained 
  through the steps described in section [blah](#blah-ref) below
* The results for WASP from Table 4 and Table 5 can be 
  obtained through the steps described in section [blah](#blah-ref) below
* All the results from Table 6 can be obtained by executing
  the commands enumerated in section [blah](#blah) below
 
* Which data or conclusions from the paper are generated/supported by the artifact components?
* Which activities described in the paper have led to the creation of the artifact components?
* What is the functionality/purpose of the artifact (in case it goes beyond answering the previous 2 questions)? 

Please provide explicit references that link processes, data, or conclusions in the paper with the location of the supporting component in the artifact, e.g., 

* “The data in table 1 can be obtained by running script ‘abc.sh’ on the data at ‘/home/anonymous/input_data.csv’”
* “Performing the described literature analysis on all articles listed in /home/anonymous/papers.csv led to the classification in /home/anonymous/papers_tagged.json”

## For authors claiming a reusable badge: What are the authors' claims about the artifact's reusability to be evaluated by the committee?

TODO:

* The three symbolic test suites described in Section 5 of our 
  paper can be repurposed for other static analysis tools for Wasm.
* WASP described in Section 3 of our paper ...

Example:

* “The implementation can easily be modified to use a different algorithm than the one described in section 4.1 of our paper by implementing a corresponding module. We provide an interface specification in ...”

## For authors claiming an available badge

TODO: 

We offer to publish the artifact on [DARTS](https://drops.dagstuhl.de/opus/institut_darts.php), in which case the available badge will be issued automatically.
If you agree to publishing your artifact under a Creative Commons license, please indicate this here.
You do not need to answer any of the following questions in this case.

In case you would like to publish your artifact under different conditions, please provide the following information.

* On which platform will the artifact be made publicly available?
* Please provide a link to the platform’s retention policy (not required for DARTS, Zenodo, FigShare).
* Under which license will the artifact be published?

## Artifact Requirements

Please list any specific hardware or software requirements for accessing your artifact

* `docker` 
* 123

## Getting Started

### Setup Docker

Load the `wasp/wasp` docker image by running the following command:

```sh
docker load --input wasp.tar.gz 
```

This command may take upwards of 20 minutes. Next, create a 
temporary container and gain shell access:

```sh
docker run --rm -ti --ulimit='stack=-1:-1'--cpus=<value> wasp/wasp
```

If this worked correctly your shell prompt should have 
changed and you will be the **wasp** user:

```sh
wasp@bba52544d0c0:~$ whoami
wasp
wasp@bba52544d0c0:~$
```

You can now try running WASP and WASP-C inside the container,
where you should see an output similar to:

```sh
wasp@11194b4b99bd:~$ wasp -v
WebAssembly Symbolic Processor v0.2
wasp@11194b4b99bd:~$ wasp-c -v
version 0.1
wasp@11194b4b99bd:~$
```

Now you can use WASP to concolically execute Wasm programs:

```sh
```

#### Layout(#layout)


```
.
├── Collections-C/
├── Gillian/
├── Test-Comp/
├── test-suite-validator/
├── aws-encryption-sdk/
├── wasp/
├── wasp-c/
├── Dockerfile
└── ECOOP22_AE_Submission_Document.md
```

* describe dirs

### EQ1: Collections-C

If needed clone the repository through:

```sh
git clone https://github.com/wasp-platform/Collections-C.git
```

Then, go into the **Collections-C** directory:

```sh
cd Collections-C # or cd /home/wasp/Collections-C
```

#### Table 2

To obtain the results from Table 2 for WASP run the following 
command:

```sh
./run.py
```

The script terminates after around 60s and creates a file called 
`table.csv`, which contains the results for Table 2 for WASP.
To obtain the results for only one row of the table point 
the script to the desired category:

```sh
./run.py _build/for-wasp/normal/array # runs only Array
./run.py _build/for-wasp/normal/queue # runs only Queue
...
```

The script always outputs the results to the file `table.csv`, 
meaning that consecutive runs will continuously overwrite the file 
`table.csv`. Additionally, between runs delete the `output` directory 
to eliminate the possibility of conflicts in the results.

To obtain the results from Table 2 for Gillian:

1. Go into the Gillian directory: `cd ../Gillian` or `cd /home/wasp/Gillian`
2. Run for each category in `../collections-c-for-gillian/for-gillian/normal`: 

```sh
time esy x gillian-c bulk-wpst ../collections-c-for-gillian/for-gillian/normal/array/ \
  -I ../collections-c-for-gillian/lib/include/ \
  -S ../collections-c-for-gillian/lib \
  -I ../collections-c-for-gillian/for-gillian/test-utils/ \
  -S ../collections-c-for-gillian/for-gillian/test-utils/ --ignore-undef
```

The times in the table are the one reported by the command `time`.

#### Table 3

To obtain the results from Table 3 for WASP run the following command
(inside the directory `/home/wasp/Collections-C`):

```sh
./run.py _build/for-wasp/bugs
```

These tests are supposed to return `false` since they have bugs.

To obtain the results from Table 3 for Gillian:

1. Go into the Gillian directory: `cd ../Gillian` or `cd /home/wasp/Gillian`
2. Run:

```sh
time esy x gillian-c bulk-wpst ../collections-c-for-gillian/for-gillian/bugs \
  -I ../collections-c-for-gillian/lib-with-bugs/include/ \
  -S ../collections-c-for-gillian/lib-with-bugs/ \
  -I ../collections-c-for-gillian/for-gillian/test-utils/ \
  -S ../collections-c-for-gillian/for-gillian/test-utils/ --ignore-undef
```

### EQ2: Test-Comp

If needed clone the repository through:

```sh
git clone https://github.com/wasp-platform/Test-Comp.git
```

Go into the **Test-Comp** directory:

```sh
cd Test-Comp # or cd /home/wasp/Test-Comp
```

Next, compile our *glibc* implementation and the symbolic 
test suite:

```sh
make -C lib           # Compiles bin/libc.a
```

#### Table 4

To compile the `array-fpi` sub-category of `Arrays` run:

```sh
make -C for-wasp/array-fpi -j4
```

Alternatively, one can compile the entire benchmark suite with:

```sh
make [ <THREADS=n> ]  # Compiles test suite into _build/
```

Note that, one can specify the number of threads (`n`) used 
during compilation with the optional argument `THREADS`.
It is recommended that `THREADS>=8` to speedup 
compilation (`make THREADS=8`).

Then, to run the test-suite on a category run:

```sh
python3 -m validator <THREADS> <TYPE> <CATEGORY>
```

Where, `THREADS` is an optional argument denoting the number
of analysis processes to be launched, `TYPE` is the
type of task to analyse (e.g., `branches` or `error`), and 
`CATEGORY` is the category from Table 4 to run (e.g., `Arrays` 
to execute `C1.Arrays` and `all` to run all categories).

For example, since we compiled `array-fpi` from `Arrays`, 
we can run:

```sh
python3 -m validator 4 error Arrays # Executes Cover-Error with 8 threads on sub-category C1.Arrays
python3 -m validator 4 branches Arrays # Executes Cover-Branches with 8 threads on sub-category C1.Arrays
python3 -m validator 4 error all # Executes Cover-Branches with 8 threads on all compiled categories 
```

IMPORTANT! Since these benchmarks take a considerable 
amount of time to execute, the `validator` does not 
repeat tasks when re-running the same command. To 
generate new values one must delete the directory
`test-suite` before the executing the `validator`.
Additionally, for `branches` the `validator` might
only output to `stdout` after 15 mins, meaning 
that the tool reached the timeout. For this reason,
we recommend running the benchmarks that do not timeout
as often: `python3 -m validator 4 error Arrays`.
At the start of a category the `validator` displays the number 
of categories remaining, and for each line of the output, the 
current executed tests over the total number of tests.

Lastly, to obtain the results from Table 4 for Cover-Error run:

```sh
python3 scripts/coverage.py test-suite/coverage-error-call error > error.csv
```

And for Cover-Branches:

```sh
python3 scripts/coverage.py test-suite/coverage-branches branches > branches.csv
```

In our example, the contents in `error.csv` after executing
the command `python3 -m validator 4 error Arrays` and 
compiling only `array-fpi` (`make -C for-wasp/array-fpi -j4`), are:

```
Category,WASP,Time
Arrays,69.0/69,7.613090000000001
BitVectors,0/0,0.0
ControlFlow,0/0,0.0
ECA,0/0,0.0
Floats,0/0,0.0
Heap,0/0,0.0
Loops,0/0,0.0
Recursive,0/0,0.0
Sequentialized,0/0,0.0
XCSP,0/0,0.0
Combinations,0/0,0.0
MainHeap,0/0,0.0
```

IMPORTANT! Note that, to replicate all the numbers of WASP on the table
one must compile all the symbolic test suite and subsequently run the 
validator on `all` for `error` and `branches`. However, as we have reported 
in the paper this can take over 300hours.

#### Table 5

The CPU times for WASP in Table 5 are acquired from the sum of the
`Time` column in `error.csv` and `branches.csv`.

### EQ3: AWS Encryption SDK for C

If needed clone the repository through:

```sh
git clone https://github.com/wasp-platform/aws-cryptosdk-c.git
```

First, go into the **AWS Encryption SDK for C** directory:

```sh
cd aws-cryptosdk-c # or cd /home/wasp/aws-cryptosdk-c
```

Next, compile our *glibc* implementation and the symbolic 
test suite:

```sh
make -C lib           # Compiles bin/libc.a
```

#### Table 6

To compile the verification proofs into symbolic tests simply 
run:

```sh
make
```

The Makefile will output some warnings which shouldn't be of 
concern.
If everything worked, the proofs were compiled into `_build/tests`.
Next, you can run the category `Md` by running the command:

```sh
./run.py $(cat mappings/md.txt)
```

This command will save the summarised results in the file `table.csv`.
Then, the results from the row **Md** in Table 6 are obtained by summing 
the columns of the file `table.csv`. The remaining rows from Table 6
can be obtained analogously by passing different file mappings from 
the directory `mappings` to `./run.py`.
