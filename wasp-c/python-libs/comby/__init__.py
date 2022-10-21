# -*- coding: utf-8 -*-
"""
This package provides a set of Python bindings for Comby, a general purpose
tool for matching and rewriting code in arbitrary languages.
"""
from loguru import logger as _logger

from . import exceptions
from .core import Location, LocationRange, BoundTerm, Environment, Match
from .binary import CombyBinary

Comby = CombyBinary

__version__ = '0.0.2'

_logger.disable('comby')
