# README

## Tools

* [WebAssembly Symbolic Processor](wasp/README.md)
* [WASP-C](wasp-c/README.md)

## Reproducing Results

### Setup

From the root of the project first build the `wasp/wasp`
docker image by running the following command:

```sh
docker build -t wasp/wasp .
```

IMPORTANT! This command may take upwards of x minutes since
it requires installing all dependencies of *Gillian*. If one
does not want to install Gillian comment the lines 46-49
in `Dockerfile`.

Next, create a temporary container and gain shell access:

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

To obtain the results from Table 2 for WASP run the command 
(inside the directory `/home/wasp/Collections-C`):

```sh
./run.py
```

This test script will create a file called `table.csv` with 
the results summarised.
To obtain the results for only one row of the table point 
the script to the desired category:

```sh
./run.py _build/for-wasp/normal/array # runs only Array
./run.py _build/for-wasp/normal/queue # runs only Queue
...
```

Note that, this script always outputs the results to 
the file `table.csv`, meaning that consecutive runs will 
continuously overwrite the file `table.csv`.
Importantly, between runs delete the `output` directory to 
eliminate the possibility of conflicts in the results.

To obtain the results from Table 2 for Gillian:

1. Go into the Gillian directory: `cd ../Gillian` or `cd /home/wasp/Gillian`
2. Run for each directory in `../collections-c-for-gillian/for-gillian/normal`: 

```sh
time esy x gillian-c bulk-wpst ../collections-c-for-gillian/for-gillian/normal/array/ \
  -I ../collections-c-for-gillian/lib/include/ \
  -S ../collections-c-for-gillian/lib \
  -I ../collections-c-for-gillian/for-gillian/test-utils/ \
  -S ../collections-c-for-gillian/for-gillian/test-utils/ --ignore-undef
```

#### Table 3

To obtain the results from Table 3 for WASP run the command
(inside the directory `/home/wasp/Collections-C`):

```sh
./run.py _build/for-wasp/bugs
```

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

Generating the following in `error.csv` if we execute the
command `python3 -m validator 4 error Arrays` after 
compiling only `array-fpi` (`make -C for-wasp/array-fpi -j4`):

```
Category,WASP,Time
Arrays,47.0/69,7.613090000000001
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

If everything worked, the proofs were compiled into `_build/tests`.
Next, you can run the category `Md` by running the command:

```sh
./run.py $(cat mappings/md.txt)
```

This command will record the summarised results in a file `table.csv`.
The results from the row **Md** in Table 6 are obtained by summing 
the columns of the file in `table.csv`. The remaining rows from Table 6
can be obtained analogously by passing different file mappings from 
directory `mappings` to `./run.py`.
