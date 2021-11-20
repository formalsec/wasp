from __future__ import annotations

import time
import resource
import subprocess

from wasp import logger as logging

class WASP:
    def __init__(
            self, 
            instr_limit=4611686018427387803,
            time_limit=900,                  # default 15mins
            memory_limit=15*1024*1024*1024   # default 15Gib
        ):
        self.instr_limit: int = instr_limit
        self.time_limit: int = time_limit
        self.memory_limit: int = memory_limit

    @staticmethod
    def limit_ram(limit) -> None:
        resource.setrlimit(resource.RLIMIT_AS, (limit, limit))

    def cmd(self, test_prog: str, output_dir: str = "") -> list[str]:
        output_cmd = []
        if not output_dir == "":
            output_cmd = ['-r', output_dir]
        return [
            'wasp',
            test_prog,
            '-e',
            '(invoke \"__original_main\")',
            '-m',
            str(self.instr_limit),
            '-t'
        ] + output_cmd

    def run(self, test_file: str, output_dir: str = "", instr_limit=None, \
            time_limit=None) -> ExecutionResult:
        # set options
        if not instr_limit is None:
            self.instr_limit = instr_limit
        if not time_limit is None:
            self.time_limit = time_limit

        time_start = time.time()

        output = None
        crashed = False
        timeout = False
        cmd = self.cmd(test_file, output_dir)
        logging.debug(f'WASP.run:cmd=\'{cmd}\'')
        try: 
            output = subprocess.check_output(
                    cmd,
                    timeout=self.time_limit, 
                    stderr=subprocess.STDOUT,
                    preexec_fn=(lambda: WASP.limit_ram(self.memory_limit))
                )
            output = output.decode()
        except subprocess.TimeoutExpired:
            timeout = True
        except subprocess.CalledProcessError:
            crashed = True

        total_time = time.time() - time_start
        return ExecutionResult(
            test_file, 
            output, 
            crashed, 
            timeout, 
            total_time
        )

class ExecutionResult:
    def __init__(
            self,
            fileName: str,
            stdout,
            crashed: bool,
            timeout: bool,
            time
        ):
        self.fileName = fileName
        self.stdout = stdout
        self.crashed = crashed
        self.timeout = timeout
        self.time = time
