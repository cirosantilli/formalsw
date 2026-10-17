"""
Ordinary methods mutate the instance observed by every alias.
"""


class Counter:
    def __init__(self, start: int = 0) -> None:
        self.value: int = start
        self.history: list[int] = []

    def advance(self, amount: int) -> int:
        self.value += amount
        self.history.append(self.value)
        return self.value


def shared(n: int) -> int:
    """
    @formalsw: Returns
    """
    counter = Counter(n)
    alias = counter
    first = counter.advance(2)
    return alias.advance(first)
