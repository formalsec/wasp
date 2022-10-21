# -*- coding: utf-8 -*-
"""
This module provides definitions for the exceptions raised by Comby.
"""
import attr


class CombyException(Exception):
    """Base class used by all Comby exceptions."""


class ConnectionFailure(CombyException):
    """
    The client failed to establish a connection to the server within the
    allotted connection timeout window.
    """


@attr.s(auto_exc=True)
class CombyBinaryError(CombyException):
    """An error was produced by the Comby binary.

    Attributes
    ----------
    code: int
        The exit code that was produced by the binary.
    message: str
        The error message that was produced by the binary.
    """
    code = attr.ib(type=int)
    message = attr.ib(type=str)
