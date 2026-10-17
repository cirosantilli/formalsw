#!/usr/bin/env python3
"""Termination is a proof about all executions, not a timeout experiment."""


def forever() -> None:
    """A supported infinite execution.

    @cleanxy: Not Halts
    @cleanxy: theorem diverges_forever : diverges(this_function())
    """
    while True:
        pass


def gcd_subtract(a: int, b: int) -> int:
    """Euclid's subtraction algorithm for positive inputs; otherwise return zero.

    Each subtraction preserves positivity and strictly decreases a + b.
    Neither a fixed number of iterations nor a timeout proves this theorem.

    @cleanxy: Returns
    """
    if a <= 0:
        return 0
    if b <= 0:
        return 0
    while a != b:
        if a > b:
            a -= b
        else:
            b -= a
    return a


def implicit_none() -> None:
    """Falling off the end is successful termination.

    @cleanxy: Returns
    """
    pass


def explicit_none() -> None:
    """Explicit and implicit None have the same termination behavior.

    @cleanxy: Returns
    """
    return None


def bare_return() -> None:
    """A bare return is successful too.

    @cleanxy: Returns
    """
    return
