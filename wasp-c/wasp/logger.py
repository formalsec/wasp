import logging

from sys import stdout
from copy import copy

# levels
DEBUG = logging.DEBUG
INFO = logging.INFO
WARNING = logging.WARNING
ERROR = logging.ERROR
CRITICAL = logging.CRITICAL

MAPPING = {
    'DEBUG'    : 37,
    'INFO'     : 36,
    'WARNING'  : 33,
    'ERROR'    : 31,
    'CRITICAL' : 41
}

PREFIX = '\033[1m\033['
SUFFIX = '\033[0m'

class ColoredFormatter(logging.Formatter):

    def __init__(self, fmt):
        logging.Formatter.__init__(self, fmt)

    def format(self, record):
        colored_record = copy(record)
        levelname = colored_record.levelname
        seq = MAPPING.get(levelname, 37)
        colored_record.levelname = f'{PREFIX}{seq}m{levelname}{SUFFIX}'
        return logging.Formatter.format(self, colored_record)

def init(log, level):
    handler = logging.StreamHandler(stdout)
    log_fmt = '[%(levelname)s][%(name)s] %(message)s (%(filename)s:%(lineno)d)'
    handler.setFormatter(ColoredFormatter(fmt=log_fmt))
    log.setLevel(level)
    log.addHandler(handler)
