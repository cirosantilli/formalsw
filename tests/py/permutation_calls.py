from itertools import permutations


def count(xs: list[int]) -> int:
    """
    @formalsw: Returns
    """
    total = 0
    for p in permutations(xs):
        total += 1
    return total
