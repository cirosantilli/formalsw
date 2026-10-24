def present(text: str, substring: str) -> bool:
    """
    @formalsw: Returns
    """
    return substring in text


def absent(text: str, substring: str) -> bool:
    """
    @formalsw: Returns
    """
    return substring not in text
