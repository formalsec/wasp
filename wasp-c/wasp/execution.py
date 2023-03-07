import time
import logging
import resource
import subprocess

log = logging.getLogger(__name__)

class WASP:
    def __init__(self, config, verbose=False):
        self.engine = config["tool"]
        self.config = config
        self.verbose = verbose

    @staticmethod
    def limit_ram(limit):
        resource.setrlimit(resource.RLIMIT_AS, (limit, limit))

    def get_args(self, output):
        args = []
        if not self.config["type_checker"]:
            args.append("-u")
        if self.config["debug"]:
            args.append("-t")
        args += [
            "--policy", self.config["policy"],
            "--timeout", str(self.config["timeout"]),
            "--workspace", output
        ]
        return args + self.config["additional_args"]

    def run(self, file, func, output, timeout=900, memout=15*1024*1024*1024):
        time_start = time.time()
        crashed, timed = False, False
        stdout, stderr = None, None
        try:
            args = self.get_args(output)
            cmd = [self.engine, file, "-e", f"(invoke \"{func}\")"] + args
            log.debug(f"WASP args: \"{cmd}\"")
            result = subprocess.run(
                cmd,
                text=True,
                check=True,
                capture_output=True,
                timeout=timeout,
                preexec_fn=(lambda: WASP.limit_ram(memout))
            )
            stdout, stderr = result.stdout, result.stderr
        except subprocess.CalledProcessError as e:
            crashed = True
            stdout, stderr = e.stdout, e.stderr
        except subprocess.TimeoutExpired as e:
            timed = True
            stdout, stderr = e.stdout, e.stderr

        total_time = time.time() - time_start
        return ExecutionResult(file, stdout, stderr, crashed, timed,
                               total_time)

class ExecutionResult:
    def __init__(self, filename, stdout, stderr, crashed, timeout, time):
        self.filename = filename
        self.stdout = stdout
        self.stderr = stderr
        self.crashed = crashed
        self.timeout = timeout
        self.time = time
