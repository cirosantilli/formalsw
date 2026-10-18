from math import gcd as common_divisor


def pair(a: int, b: int) -> int:
    """
    @formalsw: Returns
    """
    return common_divisor(a, b)


def empty() -> int:
    """
    @formalsw: Returns
    """
    return common_divisor()


def single(n: int) -> int:
    """
    @formalsw: Returns
    """
    return common_divisor(n)


def booleans(a: bool, b: bool) -> int:
    """
    @formalsw: Returns
    """
    return common_divisor(a, b)


def invalid_after_one(value: str) -> int:
    """
    @formalsw: theorem throws (value : String) : Throws(this_function(value))
    """
    return common_divisor(1, value)
