# Concolic Execution for WebAssembly

The artifact includes:

* The source code of Gillian, WASP, and WASP-C
* The benchmarks on which we evaluate our tools:
  * Collections-C
  * Test-Comp
  * AWS Amazon Encryption SDK for C

## For authors claiming a functional or reusable badge: What are claims about the artifact’s functionality to be evaluated by the committee?

The artifact includes scripts for reproducing the results documented
in Section 4 of the paper; more specifically: Tables 1-6.

* All the results from Table 1 can be obtained through the 
  steps described in section [EQ1](#eq1-comparison-with-manticore) below
* All the results from Table 2 and Table 3 can be obtained 
  through the steps described in section [EQ2](#eq2-collections-c) below
* All the results from Table 4 can be obtained through the 
  steps described in section [EQ3](#eq3-test-comp) below
* All the results from Table 5 can be obtained through the 
  steps described in section [EQ4](#eq4-optimisations)
* All the results from Table 6 can be obtained by executing
  the commands enumerated in section [EQ5](#eq5-aws-encryption-sdk-for-c) below
 
## For authors claiming a reusable badge: What are the authors' claims about the artifact's reusability to be evaluated by the committee?

* The artifact can be used to run WASP-C on any other C program 
  annotated with assumptions and assertions. See [examples](#examples) to 
  check how to do this.
* The symbolic test suites that result from the compilation of 
  our C benchmarks can be used to evaluate other symbolic 
  execution tools for Wasm.

## Artifact Requirements

* Recommended: 
  * 33GiB Ram
  * 60GiB disk space
  * CPU >= Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz:
    * at least 8 cores
  * These requirements can reproduce all the results in our 
    paper

## Getting Started

### Setup Docker

Load the `wasp/wasp` docker image by running the following command:

```sh
docker pull ghcr.io/wasp-platform/wasp:latest 
```

This command may take upwards of 20 minutes. Next, create a 
temporary container and gain shell access (allocate enough 
`--cpus=8` to run the bigger benchmarks):

```sh
docker run --rm -ti --ulimit='stack=-1:-1' --cpus=<value> ghcr.io/wasp-platform/wasp:latest
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

#### Examples

**WASP Example:**

Now you can use WASP to concolically execute Wasm programs;
for example, in order to execute the Wasm test 
`/home/wasp/wasp/tests/regression/assume_assert.wast` 
run the following command:

```sh
wasp wasp/tests/regression/assume_assert.wast -t
```

Will create a directory `output`, containing a report 
(`output/report.json`) and another directory with the 
concrete test suite generated (`output/test_suite`). 
To analyse the generated report, use the command:

```sh
python3 -m json.tool output/report.json 
```

Verify that the outputs change by editing the `assume_assert.wast` test 
(e.g., `vim wasp/tests/regression/assume_assert.wast`) 
by changing the instruction `i32.eq` in line 12 to 
`i32.lt_s` and the instruction `i32.ne` in line 16
to `i32.ge_s`. Next, re-run `wasp` on the file and
inspect the new outputs in `output`.


**WASP-C Example**: 

To test `wasp-c` run: 

```sh
rm -rf output
wasp-c wasp-c/tests/test01.c
```

#### Layout

The artifact has the following directories:

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

Which are comprised of:

* **Collections-C**: containing code for Collections-C and its
  symbolic test suite 
* **Gillian**: containing code for the gillian-c tool
* **Test-Comp**: containing code for the Test-Comp symbolic 
  test suite
* **test-suite-validator**: containing code for the TestCov test 
  suite validation tool.
* **aws-encryption-sdk**: containing the code of AWS Encryption SDK 
  for C and its symbolic test suite
* **wasp**: containing the code of WASP
* **wasp-c**: containing the code of WASP-C


### EQ1: Comparison with Manticore

To obtain the results from **Table 1**, first install manticore:

```sh
sudo pip install manticore 
```

then run:

```sh
cd /home/wasp/wasp && ./tests/run.py
```

When it is finished, the results for WASP will be in the table
`/home/wasp/wasp/wasp_output/results-btree-wasp.csv`, and the
results for Manticore will be in the table 
`/home/wasp/wasp/mcore_output/results-btree-mcore.csv`.

### EQ2: Collections-C

#### Table 2

To obtain the results from **Table 2 for WASP**, go into the 
**Collections-C** directory and run the following command:

```sh
cd /home/wasp/Collections-C
time ./run.py --normal
```

The script terminates after around 60s and creates a file called 
`results_normal.csv`, that contains the results from Table 2 for WASP.

To obtain the results for only one row of the table, point 
the script to the desired category:

```sh
./run.py --single _build/for-wasp/normal/array # runs only Array
./run.py --single _build/for-wasp/normal/queue # runs only Queue
...
```

Each of these commands will, respectively, create the files 
`results_array.csv` and `results_queue.csv`. In order to avoid
possible conflicts between results, it is recommended to delete 
the `output` directory before running the script.

To obtain the results from **Table 2 for Gillian-C**, first run:

```
sudo npm install -g esy@0.6.6 --unsafe-perm && cd /home/wasp/Gillian && \
  git checkout 2cb5f8d73baf7f7a811b0be6044d533a62c3f50 && esy install && esy
```

Then, run EITHER:

```sh
cd /home/wasp/Gillian
time esy x gillian-c bulk-wpst ../collections-c-for-gillian/for-gillian/normal/ \
  -I ../collections-c-for-gillian/lib/include/ \
  -S ../collections-c-for-gillian/lib \
  -I ../collections-c-for-gillian/for-gillian/test-utils/ \
  -S ../collections-c-for-gillian/for-gillian/test-utils/ --ignore-undef
```

to execute all categories of the benchmark, OR:

```sh
cd /home/wasp/Gillian
time esy x gillian-c bulk-wpst ../collections-c-for-gillian/for-gillian/normal/array \
  -I ../collections-c-for-gillian/lib/include/ \
  -S ../collections-c-for-gillian/lib \
  -I ../collections-c-for-gillian/for-gillian/test-utils/ \
  -S ../collections-c-for-gillian/for-gillian/test-utils/ --ignore-undef
```

to execute only the `array` category. Analogously, one may 
individually execute the other categories by pointing the 
above command to their corresponding directories in
`../collections-c-for-gillian/for-gillian/normal/`; by 
replacing `array` in the first line with the name of the 
category.

Lastly, the execution time for Gillian-C reported in the 
table is the one outputted by the `time` command.

#### Table 3

To obtain the results from **Table 3 for WASP** run the following 
commands:

```sh
cd /home/wasp/Collections-C
./run.py --bugs
```

Note that, these tests are supposed to return false since they
have bugs.

To fix the bug in the test `array_test_remove` edit the line 279 
in the `lib-with-bugs/array.c` (`vim lib-with-bugs/array.c`) to: 

```c
size_t block_size = (ar->size - 1 - index) * sizeof(void*);
```

Then, clean, compile, and run the benchmarks:

```sh
make clean
make
./run.py --bugs
```

Note that, since we fixed the bug in `array.c`, WASP now
reports that the test passed, i.e., returns `true`.

Finally, to obtain the results from **Table 3 for Gillian** run:

```sh
cd /home/wasp/Gillian
time esy x gillian-c bulk-wpst ../collections-c-for-gillian/for-gillian/bugs \
  -I ../collections-c-for-gillian/lib-with-bugs/include/ \
  -S ../collections-c-for-gillian/lib-with-bugs/ \
  -I ../collections-c-for-gillian/for-gillian/test-utils/ \
  -S ../collections-c-for-gillian/for-gillian/test-utils/ --ignore-undef
```

### EQ3: Test-Comp

Go into the **Test-Comp** directory and compile our *glibc*
implementation:

```sh
cd /home/wasp/Test-Comp
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
./bin/validator [-h] [-j JOBS] [-branches] [-error] [--output OUTPUT] category
```

Where: `JOBS` is an optional argument denoting the number
of analysis processes to be launched, `-branches` and `-error` are the
type of task to analyse (e.g., `cover-branches` or `cover-error`), and 
`category` is the category from Table 4 to run (e.g., `Arrays` 
to execute `C1.Arrays` and `all` to run all categories).

For example, since we compiled `array-fpi` from `Arrays`, 
we can run:

```sh
./bin/validator -j 4 -error Arrays # Executes Cover-Error with 4 threads on sub-category C1.Arrays
./bin/validator -j 4 -branches Arrays # Executes Cover-Branches with 4 threads on sub-category C1.Arrays
./bin/validator -j 4 -error all # Executes Cover-Branches with 4 threads on all compiled categories 
```

**IMPORTANT!** The `validator` does not repeat tasks when re-running 
the same command. To generate new values one must delete the 
directory `/home/wasp/Test-Comp/test-suite` before the executing 
the `validator`. Additionally, the `-branches` tasks may only 
output to `stdout` after 15 mins, corresponding to the default timeout. 
For this reason, we recommend running the benchmarks that do not 
timeout: `./bin/validator -j 4 -error Arrays`.

Lastly, to obtain the results used in Table 4 for Cover-Error, in `csv` format, run:

```sh
python3 scripts/coverage.py test-suite/coverage-error-call error > error.csv
```

And for Cover-Branches:

```sh
python3 scripts/coverage.py test-suite/coverage-branches branches > branches.csv
```

In the example above, the contents in `error.csv` will be:

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

To replicate all the numbers of WASP on the table one must compile all 
the symbolic test suite and subsequently run the `validator` with the 
category `all` for both `-error` and `-branches`. However, as we have 
reported in the paper this can take over 300 hours. Hence, we recommend 
doing it one category at the time, starting with the categories that 
take less time. 

#### Table 5

The CPU times for WASP in Table 5 are obtained from the sum of the
`Time` column in `error.csv` and `branches.csv`.

### EQ4: Optimisations

First, make sure the benchmarks of Test-Comp were all compiled as 
described in the previous evaluation question [EQ3](#eq3-test-comp). Then, 
to obtain the results from **Table 5**, simply run:

```sh
cd /home/wasp/Test-Comp && ./scripts/run_lists.sh
```

When, the script is finished the results will be in the table 
`/home/wasp/Test-Comp/results/table3.csv`.

### EQ5: AWS Encryption SDK for C

#### Table 6

Go into the **AWS Encryption SDK for C** directory and compile
our *glibc* implementation and test suite:

```sh
cd /home/wasp/aws-encryption-sdk
make -C lib
make
```

If everything worked, the proofs were compiled into `_build/tests`.
Next, you can run the category `Md` using the command:

```sh
./run.py $(cat mappings/md.txt)
```

This command will save the summarised results into the file `table.csv`.
Then, the results from the row **Md** in Table 6 are obtained by summing 
the columns of the file `./table.csv`. The remaining rows from Table 6
can be obtained analogously by passing different file mappings from 
the directory `mappings` to `./run.py`. For instance, to obtain the
results for the **Decrypt** category use:

```sh
./run.py $(cat mappings/decrypt.txt)
```

All possible categories:

```
/home/wasp/aws-encryption-sdk/mappings/
├── cmm.txt
├── decrypt.txt
├── edk.txt
├── keyring.txt
├── md.txt
├── misc-ops.txt
└── private.txt
```
