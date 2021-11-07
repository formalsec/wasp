import logging

from sys import stdout

# levels
DEBUG = logging.DEBUG
INFO = logging.INFO
WARNING = logging.WARNING
ERROR = logging.ERROR
CRITICAL = logging.CRITICAL

# global logger
logger = logging.getLogger(__name__)

def create_logger(level):
    log = logging.getLogger(__name__)
    log.setLevel(level)
    handler = logging.StreamHandler(stdout)
    handler.setFormatter(logging.Formatter(fmt=logging.BASIC_FORMAT))
    log.addHandler(handler)
    return log

def init(level):
    global logger
    logger = create_logger(level)

def critical(*args, **kwargs):
    logger.critical(*args, **kwargs)


def error(*args, **kwargs):
    logger.error(*args, **kwargs)


def exception(*args, **kwargs):
    logger.exception(*args, **kwargs)


def warning(*args, **kwargs):
    logger.warning(*args, **kwargs)


def info(*args, **kwargs):
    logger.info(*args, **kwargs)


def debug(*args, **kwargs):
    logger.debug(*args, **kwargs)
