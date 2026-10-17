#!/usr/bin/env python

def double_or_throw(n: int) -> int:
    """Double even inputs and throw for odd inputs.

    @cleanxy: Equiv(double_or_throw_alt)
    """
    if n % 2 != 0:
        raise ValueError("odd input", n)
    return n * 2


def double_or_throw_alt(n: int) -> int:
    """Alternative implementation with equivalent exception behavior.

    @cleanxy: Halts
    """
    if n % 2 != 0:
        raise ValueError("odd input", n)
    return n * 2


def throw_msg_1(n: int) -> None:
    """
    This tests that different exception messages count as different function outcomes.

    @cleanxy: Halts
    @cleanxy: Not Equiv(throw_msg_2)
    """
    raise Exception('msg1')


def throw_msg_2(n: int) -> None:
    """@cleanxy: Halts"""
    raise Exception('msg2')
