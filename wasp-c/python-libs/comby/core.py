# -*- coding: utf-8 -*-
"""
This module defines several common data structures for describing code
transformations, source locations, environments, matches, and templates.
"""
__all__ = (
    'Location',
    'LocationRange',
    'BoundTerm',
    'Environment',
    'Match'
)

from typing import Dict, Iterator, Any, Mapping, Sequence

import attr


@attr.s(frozen=True, slots=True, str=False)
class Location:
    """
    Represents the location of a single character within a source text by its
    zero-indexed line and column numbers.

    Attributes
    ----------
    line: int
        Zero-indexed line number.
    col: int
        Zero-indexed column number.
    offset: int
        Zero-indexed character offset.
    """
    line = attr.ib(type=int)
    col = attr.ib(type=int)
    offset = attr.ib(type=int)

    @staticmethod
    def from_dict(d: Dict[str, Any]) -> 'Location':
        return Location(line=d['line'],
                        col=d['column'],
                        offset=d['offset'])


@attr.s(frozen=True, slots=True, str=False)
class LocationRange:
    """
    Represents a contiguous range of locations within a given source text as a
    (non-inclusive) range of character positions.

    Attributes
    ----------
    start: Location
        The start of the range.
    stop: Location
        The (non-inclusive) end of the range.
    """
    start = attr.ib(type=Location)
    stop = attr.ib(type=Location)

    @staticmethod
    def from_dict(d: Dict[str, Any]) -> 'LocationRange':
        return LocationRange(Location.from_dict(d['start']),
                             Location.from_dict(d['end']))


@attr.s(frozen=True, slots=True)
class BoundTerm:
    """Represents a binding of a named term to a fragment of source code.

    Attributes
    ----------
    term: str
        The name of the term.
    location: LocationRange
        The location range to which the term is bound.
    fragment: str
        The source code to which the term is bound.
    """
    term = attr.ib(type=str)
    location = attr.ib(type=LocationRange)
    fragment = attr.ib(type=str)

    @staticmethod
    def from_dict(d: Dict[str, Any]) -> 'BoundTerm':
        """Constructs a bound term from a dictionary-based description."""
        return BoundTerm(term=d['variable'],
                         location=LocationRange.from_dict(d['range']),
                         fragment=d['value'])


class Environment(Mapping[str, BoundTerm]):
    @staticmethod
    def from_dict(ts: Sequence[Dict[str, Any]]) -> 'Environment':
        return Environment([BoundTerm.from_dict(bt) for bt in ts])

    def __init__(self, bindings: Sequence[BoundTerm]) -> None:
        self.__bindings = {b.term: b for b in bindings}

    def __repr__(self) -> str:
        s = "comby.Environment([{}])"
        return s.format(', '.join([repr(self[t]) for t in self]))

    def __len__(self) -> int:
        """Returns the number of bindings in this environment."""
        return len(self.__bindings)

    def __iter__(self) -> Iterator[str]:
        """Returns an iterator over the term names in this environment."""
        return self.__bindings.keys().__iter__()

    def __getitem__(self, term: str) -> BoundTerm:
        """Fetches details of a particular term within this environment.

        Parameters:
            term: the name of the term.

        Returns:
            details of the source to which the term was bound.

        Raises:
            KeyError: if no term is found with the given name.
        """
        return self.__bindings[term]


@attr.s(slots=True, frozen=True)
class Match(Mapping[str, BoundTerm]):
    """
    Describes a single match of a given template in a source text as a mapping
    of template terms to snippets of source code.

    Attributes
    ----------
    matched: str
        the source text that was matched.
    location: LocationRange
        the range of location range that was matched.
    environment: Environment
        the associated environment, mapping template terms to snippets in the
        source text, for the match.
    """
    matched = attr.ib(type=str)
    location = attr.ib(type=LocationRange)
    environment = attr.ib(type=Environment)

    @staticmethod
    def from_dict(d: Dict[str, Any]) -> 'Match':
        return Match(matched=d['matched'],
                     location=LocationRange.from_dict(d['range']),
                     environment=Environment.from_dict(d['environment']))

    def __len__(self) -> int:
        """Returns the number of bindings in the environment."""
        return len(self.environment)

    def __iter__(self) -> Iterator[str]:
        """Returns an iterator over the term names in the environment."""
        yield from self.environment

    def __getitem__(self, term: str) -> BoundTerm:
        return self.environment[term]
