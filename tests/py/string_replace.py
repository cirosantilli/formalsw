def replace(text: str, old: str, new: str, count: int) -> str:
    """
    @formalsw: Requires(-2147483648 <= count <= 2147483647)
    @formalsw: Returns
    """
    return text.replace(old, new, count)


def replace_all(text: str, old: str, new: str) -> str:
    """
    @formalsw: Returns
    """
    return text.replace(old, new)
