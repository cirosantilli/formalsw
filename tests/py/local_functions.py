from __future__ import annotations


def shifted(n: int) -> int:
    """
    @formalsw: Returns
    """
    offset = n

    def add(x: int) -> int:
        return x + offset

    offset += 1
    return add(n)


def shared(n: int) -> int:
    items = [n]

    def append(x: int) -> int:
        items.append(x)
        return items[0] + items[1]

    old = items
    items = [n + 1]
    result = append(n + 2)
    return result + old[0]
