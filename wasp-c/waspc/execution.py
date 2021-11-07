import time
import resource
import subprocess

class WASP:
    def __init__(
            self, 
            binPath,
            instrLimit=4611686018427387803,
            timeLimit=900,                  # default 15mins
            memoryLimit=15*1024*1024*1024   # default 15Gib
        ):
        self.binPath = binPath
        self.instrLimit = instrLimit
        self.timeLimit = timeLimit
        self.memoryLimit = memoryLimit

    def getInstrLimit(self):
        return self.instrLimit

    def setInstrLimit(self, limit):
        if limit is not None:
            self.instrLimit = limit

    def getTimeLimit(self):
        return self.timeLimit

    def setTimeLimit(self, limit):
        if limit is not None:
            self.timeLimit = limit

    def getMemoryLimit(self):
        return self.memoryLimit

    @staticmethod
    def limit_ram(limit):
        resource.setrlimit(resource.RLIMIT_AS, (limit, limit))

    def cmd(self, testFile):
        return [
            f'./{self.binPath}/wasp',
            testFile,
            '-e',
            '(invoke \"__original_main\")',
            '-m',
            str(self.instrLimit)
        ]

    def run(self, testFile, instrLimit=None, timeLimit=None):
        # set options
        self.setInstrLimit(instrLimit)
        self.setTimeLimit(timeLimit)

        time_start = time.time()

        output = None
        crashed = False
        timeout = False
        try: 
            output = subprocess.check_output(
                    self.cmd(testFile),
                    timeout=self.getTimeLimit(), 
                    stderr=subprocess.STDOUT,
                    preexec_fn=(lambda: WASP.limit_ram(self.getMemoryLimit()))
                )
            output = output.decode()
        except subprocess.TimeoutExpired:
            timeout = True
        except subprocess.CalledProcessError:
            crashed = True

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
