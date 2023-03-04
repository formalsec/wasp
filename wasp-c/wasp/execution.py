import time
import logging
import resource
import subprocess

log = logging.getLogger(__name__)

class WASP:
    def __init__(
            self,
            verbose=False,
            instr_limit=-1,
            time_limit=900,                  # default 15mins
            memory_limit=15*1024*1024*1024   # default 15Gib
        ):
        self.verbose = verbose,
        self.instr_limit  = instr_limit
        self.time_limit   = time_limit
        self.memory_limit = memory_limit

    @staticmethod
    def limit_ram(limit):
        resource.setrlimit(resource.RLIMIT_AS, (limit, limit))

    def cmd(self, prog, entry_func, args=[]):
        args.append('-u')
        if self.verbose:
            args.append('-t')
        if self.instr_limit > -1:
            args.append('-m')
            args.append(str(self.instr_limit))
        args.append('-e')
        args.append(f'(invoke \"{entry_func}\")')
        return ['wasp', prog] + args

    def run(self,
            prog,
            entry_func,
            args,
            instr_limit=None,
            time_limit=None
        ):
        # set options
        if not (instr_limit is None):
            self.instr_limit = instr_limit
        if not (time_limit is None):
            self.time_limit = time_limit

        time_start = time.time()

        crashed = False
        timeout = False
        stdout = None
        stderr = None
        cmd = self.cmd(prog, entry_func, args)
        log.debug(f"WASP command: \"{' '.join(cmd)}\"")
        try:
            result = subprocess.run(
                cmd,
                text=True,
                check=True,
                capture_output=True,
                timeout=self.time_limit,
                preexec_fn=(lambda: WASP.limit_ram(self.memory_limit))
            )
            stdout = result.stdout
            stderr = result.stderr
        except subprocess.TimeoutExpired as e:
            timeout = True
            stdout = e.stdout
            stderr = e.stderr
        except subprocess.CalledProcessError as e:
            crashed = True
            stdout = e.stdout
            stderr = e.stderr

        total_time = time.time() - time_start
        return ExecutionResult(
            filename=prog,
            stdout=stdout,
            stderr=stderr,
            crashed=crashed,
            timeout=timeout,
            time=total_time
        )

class ExecutionResult:
    def __init__(
            self,
            filename: str,
            stdout,
            stderr,
            crashed: bool,
            timeout: bool,
            time
        ):
        self.filename = filename
        self.stdout = stdout
        self.stderr = stderr
        self.crashed = crashed
        self.timeout = timeout
        self.time = time
