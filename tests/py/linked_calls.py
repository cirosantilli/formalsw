from link_reference import double as imported_double


def caller(n: int) -> int:
    """
    @formalsw: Returns
    """
    return imported_double(n) + 1
