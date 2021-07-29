import time
import resource
import subprocess

class Runner:
    def __init__(
            self, 
            instrLimit,
            timeLimit,
            memoryLimit
        ):
        self.instrLimit = instrLimit
        self.timeLimit = timeLimit
        self.memoryLimit = memoryLimit

    @staticmethod
    def limit_ram(self):
        resource.setrlimit(resource.RLIMIT_AS, 
                (self.memoryLimit, self.memoryLimit))

    def cmd(self, testFile):
        return [
            './wasp',
            testFile,
            '-e',
            '(invoke \"__original_main\")',
            '-m',
            str(self.instrLimit)
        ]

    def run(self, testFile):

        time_start = time.time()

        output = None
        crashed = False
        timeout = False
        try: 
            output = subprocess.check_output(
                    self.cmd(testFile),
                    timeout=self.timeLimit, 
                    stderr=subprocess.STDOUT,
                    preexec_fn=Runner.limit_ram
                )
        except subprocess.TimeoutExpired:
            timeout = True
        except subprocess.CalledProcessError:
            crashed = True

        output = output.decode()

        total_time = time.time() - time_start
        return ExecutionResult(
                testFile, 
                output, 
                crashed, 
                timeout, 
                total_time
            )

class ExecutionResult:
    def __init__(
            self,
            fileName,
            stdout,
            crashed,
            timeout,
            time
        ):
        self.fileName = fileName
        self.stdout = stdout
        self.crashed = crashed
        self.timeout = timeout
        self.time = time
