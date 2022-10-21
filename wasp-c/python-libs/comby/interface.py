# -*- coding: utf-8 -*-
"""
This module defines a standard interface for interacting with Comby.
"""
__all__ = ('CombyInterface',)

from typing import Iterator, Dict, Optional
import abc

from .core import Match


class CombyInterface(abc.ABC):
    """Provides a standard interface for interacting with Comby.

    Attributes
    ----------
    version: str
        The version of Comby that is provided by this interface.
    language: str
        The default language that should be assumed when dealing with source
        text where no specific language is specified.
    """
    @property
    @abc.abstractmethod
    def version(self) -> str:
        ...

    @property
    @abc.abstractmethod
    def language(self) -> str:
        ...

    @abc.abstractmethod
    def matches(self,
                source: str,
                template: str,
                *,
                language: Optional[str] = None
                ) -> Iterator[Match]:
        """Finds all matches of a given template within a source text.

        Parameters
        ----------
        source: str
            The source text to be searched.
        template: str
            The template that should be used for matching.
        language: str, optional
            Specifies the language of the source text. If no language is
            specified, then the default language associated with this
            interface will be used.

        Yields
        ------
        All matches of the given template within in the text.
        """
        ...

    @abc.abstractmethod
    def substitute(self,
                   template: str,
                   args: Dict[str, str],
                   *,
                   language: Optional[str] = None
                   ) -> str:
        """Substitutes a set of terms into a given template."""
        ...

    @abc.abstractmethod
    def rewrite(self,
                source: str,
                match: str,
                rewrite: str,
                args: Optional[Dict[str, str]] = None,
                *,
                diff: bool = False,
                language: Optional[str] = None
                ) -> str:
        """
        Rewrites all matches of a template in a source text using a rewrite
        template and an optional set of arguments to that rewrite template.
        """
        ...
