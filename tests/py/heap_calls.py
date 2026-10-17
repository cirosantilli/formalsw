def make(n: int) -> list[int]:
    """
    @formalsw: Returns
    """
    return [n]


def push(items: list[int], value: int = 10) -> list[int]:
    items.append(value)
    return items


def total(n: int) -> int:
    """
    @formalsw: Equiv(reference)
    """
    items = make(n)
    alias = push(items)
    alias.append(n)
    return items[0] + items[1] + items[2]


def reference(n: int) -> int:
    return n + 10 + n


if __name__ == '__main__':
    assert total(-7) == -4
    values = [1]
    assert push(values) is values
    assert values == [1, 10]
