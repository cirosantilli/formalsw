def reference(text: str) -> bool:
    """
    @formalsw: Returns
    """
    if not text:
        return False
    for character in text:
        if not character.isdigit():
            return False
    return True


def solve(text: str) -> bool:
    """
    @formalsw: Equiv(reference)
    @formalsw: Returns
    """
    return text.isdigit()
