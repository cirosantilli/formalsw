"""Global state is an explicit input, and updates are part of the outcome."""

offset: int = 10
total: int = 0
label: str = "ready"
enabled: bool = True


def add_offset(n: int) -> int:
    """
    @formalsw: Returns
    @formalsw: Halts
    @formalsw: Not Throws
    @formalsw: ReturnType
    @formalsw: theorem returns_with_offset (n offset : Int) :
      Returns(this_function(n))
    """
    return n + offset


def add_offset_commuted(n: int) -> int:
    """@formalsw: Equiv(add_offset)"""
    return offset + n


def advance(n: int) -> int:
    """@formalsw: Returns"""
    global total
    total += n
    return total


def advance_explicit(n: int) -> int:
    """
    @formalsw: Equiv(advance)
    @formalsw: EquivReturn(advance)
    """
    global total
    total = total + n
    return total


def advance_declared_in_branch(n: int) -> int:
    """Scope declarations apply to the whole function, even in a dead branch.

    @formalsw: Equiv(advance)
    """
    if False:
        global total
    total += n
    return total


def return_only(n: int) -> int:
    """Same returned number, but omitting the update changes behavior.

    @formalsw: Not Equiv(advance)
    """
    return total + n


def raise_before(n: int) -> int:
    raise ValueError("failure")


def raise_after(n: int) -> int:
    """An exception does not roll back global assignments.

    @formalsw: Halts
    @formalsw: Throws
    @formalsw: Not Equiv(raise_before)
    """
    global total
    total += n
    raise ValueError("failure")


def read_label() -> str:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    return label


def read_enabled() -> bool:
    """@formalsw: Returns"""
    return enabled


def local_total(n: int) -> int:
    """Ordinary assignment creates a local, leaving the module's total alone."""
    total = n
    return total


def read_total(n: int) -> int:
    return total


def parameter_named_total(total: int) -> int:
    """The argument and the other function's global are separate inputs.

    @formalsw: Not Equiv(read_total)
    """
    return total


if __name__ == "__main__":
    assert add_offset(3) == add_offset_commuted(3) == 13
    assert advance(3) == 3 and total == 3
    assert return_only(2) == 5 and total == 3
    assert advance_explicit(2) == 5 and total == 5
    try:
        raise_after(4)
    except ValueError:
        assert total == 9
    assert local_total(100) == 100 and total == 9
    assert read_label() == "ready" and read_enabled() is True
