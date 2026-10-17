def build(n: int) -> list[int]:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    items = []
    for k in range(n):
        items.append(k)
    return items


if __name__ == '__main__':
    assert build(0) == []
    assert build(4) == [0, 1, 2, 3]
