def guarded(n: int) -> bool:
    """
    @formalsw: Returns
    """
    return 0 < n < 1 // n


if __name__ == '__main__':
    assert guarded(0) is False
    assert all(guarded(n) is False for n in range(-3, 4))
