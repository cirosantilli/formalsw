def trimmed(text: str) -> str:
    """
    @formalsw: Returns
    """
    return text.strip()


def words(text: str) -> list[str]:
    """
    @formalsw: Returns
    """
    return text.split()


def normalized(text: str) -> list[str]:
    """
    @formalsw: Returns
    """
    return text.strip().split()


if __name__ == "__main__":
    assert trimmed("\u2003\tλ 😀\u3000") == "λ 😀"
    assert words("\u2003\tλ\u001c😀\u3000") == ["λ", "😀"]
    assert normalized(" \t\n ") == []
