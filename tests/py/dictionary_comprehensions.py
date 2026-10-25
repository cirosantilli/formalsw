def shifted(values: list[int], offset: int) -> dict[int, int]:
    """
    @formalsw: Returns
    """
    return {value: value + offset for value in values}


if __name__ == '__main__':
    assert shifted([], -4) == {}
    assert shifted([-3, 0, 2], -5) == {-3: -8, 0: -5, 2: -3}
    assert list(shifted([4, -2, 4, 3, -2], 7).items()) == [(4, 11), (-2, 5), (3, 10)]
