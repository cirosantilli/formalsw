from functools import lru_cache


@lru_cache(None)
def identity(items: tuple[int, ...]) -> tuple[int, ...]:
    return items


@lru_cache(None)
def nested_identity(items: tuple[tuple[int, ...], ...]) -> tuple[tuple[int, ...], ...]:
    return items


def scenario() -> bool:
    """
    @formalsw: Returns
    """
    first = tuple([17, 23])
    second = tuple([17, 23])
    reverse = tuple([23, 17])
    left = identity(first)
    right = identity(second)
    other = identity(reverse)
    return left is first and right is first and other is reverse and right is not second


def nested_scenario() -> bool:
    """
    @formalsw: Returns
    """
    first = tuple([tuple([17]), tuple([23])])
    second = tuple([tuple([17]), tuple([23])])
    left = nested_identity(first)
    right = nested_identity(second)
    return left is first and right is first and right is not second


def generator_scenario() -> bool:
    """
    @formalsw: Returns
    """
    first = tuple(i for i in range(4) if i > 0)
    second = tuple(i for i in range(1, 4))
    left = identity(first)
    right = identity(second)
    return left is first and right is first and right is not second


if __name__ == '__main__':
    assert scenario()
    assert nested_scenario()
    assert generator_scenario()
