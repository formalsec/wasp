import os
import sys
import glob
import shutil
import logging
import argparse
import subprocess

from . import info
from . import logger
from . import testcomp
from . import io
from . import instrumentor as pre
from . import postprocessor as post

from .execution import WASP

log = logging.getLogger(__name__)

def get_parser():
    parser = argparse.ArgumentParser(
        prog=info.__NAME__,
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )

    parser.add_argument("--version", "-v", action="version",
                        version=f"version {info.__VERSION__}")
    parser.add_argument("--verbose", dest="verbose", action="store_true",
                        default=False, help="show messages verbose")
    parser.add_argument("--timeout", dest="timeout", action="store", type=int,
                        default=-1, help="timelimit for analysis")
    parser.add_argument("--backend", dest="backend", action="store",
                        default=None,
                        help="path to backend engine configuration file")
    parser.add_argument("--output", "-o", dest="output_dir", action="store",
                        default="wasp-out", help="output directory to write to")
    parser.add_argument("--include", "-I", dest="includes", action="append",
                        default=[], help="include headers path")
    parser.add_argument("--source", "-S", dest="source", action="store",
                        default="", help="lib source code")
    parser.add_argument("--rm-boolops", dest="rm_boolops", action="store_true",
                        default=False, help="use short-circuit evaluation")
    parser.add_argument("--entry", dest="entry_func", action="store",
                        default="__original_main",
                        help="entry function to start analysis")
    parser.add_argument("--compile-only", dest="compile_only",
                        action="store_true", default=False,
                        help="compile the source file without running WASP")
    parser.add_argument("--postprocess", dest="postprocess", action="store",
                        default=None,
                        help="post-processing file for WASP analysis")
    parser.add_argument("--test-comp", dest="test_comp", action="store_true",
                        default=False,
                        help="test-comp instrumentation and xml test suite")
    parser.add_argument("--property", "-p", dest="property", action="store",
                        default=None, help="property file")
    parser.add_argument("--arch", dest="arch", action="store", default="32",
                        help="data model")
    parser.add_argument("file", help="file to analyse")

    return parser

def parse(argv):
    parser = get_parser()
    return parser.parse_args(argv)

def preprocess_file(src_file, dst_file, includes, rm_boolops, instrument=False):
    log.debug(f"Processing \"{src_file}\"...")
    if instrument:
        testcomp.instrument(src_file, dst_file)
        src_file = dst_file
    try:
        pre.process_file(src_file, dst_file, includes, not rm_boolops)
    except pre.ParsingError as e:
        log.error("ParsingError: " + e.message)
        return 1
    log.debug(f"Created \"{dst_file}\".")
    return 0

def configure(output_dir, root_dir, src_code, includes, entry_func):
    log.debug(f"Configuring compilation...")

    # Copy `Makefile" to `output_dir"
    src_make = os.path.join(root_dir, "share", "Makefile.main")
    dst_make = os.path.join(output_dir, "Makefile")
    log.debug(f"... Copy \"{src_make}\" to \"{dst_make}\".")
    shutil.copyfile(src_make, dst_make)

    # Create `Makefile.config"
    libs = os.path.join(root_dir, "bin")
    incl = os.path.join(root_dir, "share", "lib")
    if not os.path.exists(os.path.join(libs, "libc.a")):
        log.debug("Compiling libc.a...")
        try:
            subprocess.run(["make", "-C", incl], text=True, check=True,
                           capture_output=True)
        except subprocess.CalledProcessError as e:
            log.error(e.stdout)
            log.error(e.stderr)
            return 1
        log.debug(f"libc.a compiled to \"{libs}\"")

    conf = os.path.join(output_dir, "Makefile.config")
    log.debug(f"... Using static libc in \"{libs}\".")
    log.debug(f"... Using static libc includes in \"{incl}\".")
    log.debug(f"... Using additional includes: {includes}")
    log.debug(f"... Using additional sources in \"{src_code}\".")
    with open(conf, "w") as f:
        f.write(f"LIBC_DIR = {libs}\n")
        f.write(f"LIBC_INC = {incl}\n")
        for inc in includes:
            f.write(f"INCLUDES += -I{inc}\n")
        f.write(f"OTHER_CODE = {src_code}\n")
        f.write(f"ENTRY_FUN = {entry_func}\n")

    log.debug(f"Created \"{conf}\".")
    return 0

def compile_sources(sources):
    log.debug(f"Compiling sources in \"{sources}\"...")
    try:
        subprocess.run(["make", "-C", sources], text=True, check=True,
                       capture_output=True)
    except subprocess.CalledProcessError as e:
        log.error(e.stdout)
        log.error(e.stderr)
        return -1
    log.debug(f"Compilation done.")
    return 0

def postprocess_file(infile, outfile=None):
    log.debug(f"Processing Wasm module \"{infile}\"...")

    with open(infile, "r") as f:
        text = f.read()

    n_text = post.process(text)

    if outfile is None:
      outfile = infile

    with open(outfile, "w") as f:
        f.write(n_text)
    return 0

def get_test_suite(testsuite):
    testcases = []
    for testcase in testsuite:
        inputs = io.read_json(testcase)
        if inputs is None:
            continue
        inputs = filter(lambda t: not (("__hb" in t["name"]) or
                                       ("ternary" in t["name"])),
                        inputs)
        testcases.append(inputs)
    return testcases

def main(root_dir, argv=None):
    if argv is None:
        argv = sys.argv[1:]
    args = parse(argv)

    if args.verbose:
        logger.init(log, logging.DEBUG)
    else:
        logger.init(log, logging.INFO)

    if not os.path.exists(args.file):
        log.error(f"Input file \"{args.file}\" not found!")
        return -1

    if args.postprocess is not None:
        if len(args.postprocess) == 0:
          log.error("Output file cannot be empty!")
          return -1

        return postprocess_file(args.file, args.postprocess)

    test_comp_dir = os.path.join(args.output_dir, "test-suite")
    if args.test_comp:
        if args.property is None:
            log.error("Please specify a property file for test-comp!")
            return 1

        if not os.path.exists(test_comp_dir):
            os.makedirs(test_comp_dir)

    if not os.path.exists(args.output_dir):
        log.debug(f"Creating directory \"{args.output_dir}\"...")
        os.makedirs(args.output_dir)

    log.info("Setting up analysis files...")

    includes = args.includes + [os.path.join(root_dir, "share", "lib")]
    harness = os.path.join(args.output_dir, "instrumented_file.c")
    if preprocess_file(args.file, harness, includes, args.rm_boolops, \
                       args.test_comp) != 0:
        log.error(f"Failed to process input file \"{args.file}\"!")
        return 1

    configure(args.output_dir, root_dir, args.source, args.includes,
              args.entry_func)

    if compile_sources(args.output_dir) != 0:
        log.error(f"Failed to compile project sources!")
        return 1

    if not args.compile_only:
        wasm_harness = os.path.splitext(harness)[0] + ".wat"
        if postprocess_file(wasm_harness) != 0:
            log.error(f"Failed to annotate Wasm module!")
            return 1

        backend_file = args.backend
        if not backend_file:
            backend_file = os.path.join(root_dir, "share", "conf",
                                        "wasp-ce.json")
        backend_conf = io.read_json(backend_file)
        if not backend_conf:
            log.error(f"Failed to load backend configuration!")
            return 1

        # run WASP
        analyser = WASP(backend_conf, verbose=args.verbose)
        log.info("Starting WASP...")
        res = analyser.run(wasm_harness, args.entry_func, args.output_dir,
                           timeout=args.timeout)
        if args.verbose and res.stdout and res.stderr:
            log.debug("Exporting stdout and stdin...")
            with open(wasm_harness + ".out", "w") as out, \
                    open(wasm_harness + ".err", "w") as err:
                out.write(res.stdout)
                err.write(res.stderr)
        if res.crashed:
            log.error(f"WASP crashed")
        elif res.timeout:
            log.error(f"WASP timed out")
        if args.test_comp:
            with open(args.property, "r") as f:
                prop = f.read().rstrip()
            witnesses = os.path.join(args.output_dir, "test_suite", "witness_*.json")
            error = get_test_suite(glob.glob(witnesses))
            testcases = os.path.join(args.output_dir, "test_suite", "test_*.json")
            tests = get_test_suite(glob.glob(testcases))
            testsuite = testcomp.XMLSuiteGenerator(
                "wasp-c",
                args.file,
                prop,
                args.arch,
                error + tests
            )
            testsuite.write(os.path.join(args.output_dir, "test-suite"))
        log.info("Analysis done.")
    return 0
