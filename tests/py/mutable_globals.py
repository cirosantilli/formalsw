"""Mutable globals are shared heap inputs; annotations describe call-entry values."""
items: list[int] = []
alias = items


def push(n: int) -> None:
    """
    Append for every initial list and integer, preserving aliases.

    @formalsw: Returns
    @formalsw: Halts
    @formalsw: Not Throws
    @formalsw: ReturnType
    @formalsw: theorem returns_on_heap :
      Mutable.Heap.Valid heap →
      Mutable.Value.HasType heap (.ref items) "list[int]" →
      Returns(this_function(n))
    """
    items.append(n)


def push_via_alias(n: int) -> None:
    """
    @formalsw: Equiv(push)
    @formalsw: EquivReturn(push)
    """
    local = items
    local.append(n)


def replace(n: int) -> None:
    """Rebinding differs from mutation, even when the values match.

    @formalsw: Returns
    @formalsw: Not Equiv(push)
    """
    global items
    items = items + [n]


def push_then_raise(n: int) -> None:
    """Mutations survive exceptions.

    @formalsw: Halts
    @formalsw: Throws
    @formalsw: Not Equiv(raise_without_push)
    """
    items.append(n)
    raise ValueError("failure")


def raise_without_push(n: int) -> None:
    raise ValueError("failure")


def read_first(n: int) -> int:
    """Empty entry lists are included in the domain.

    @formalsw: Throws
    """
    return items[0] + n


def set_last(n: int) -> None:
    items[-1] = n


def read_alias(n: int) -> int:
    items.append(n)
    return len(alias)


def push_argument(other: list[int], n: int) -> int:
    """The argument and global may refer to the same list.

    @formalsw: Returns
    """
    other.append(n)
    return len(items)


def extend(n: int) -> None:
    global items
    items += [n]


def repeat(n: int) -> None:
    global items
    items *= n


def local_shadow(n: int) -> list[int]:
    items = [n]
    return items


def main():
    global items, alias
    items = [1]
    alias = items
    push(2)
    assert alias == [1, 2] and alias is items
    replace(3)
    assert items == [1, 2, 3] and alias == [1, 2] and alias is not items
    try:
        push_then_raise(4)
    except ValueError:
        assert items == [1, 2, 3, 4]
    else:
        raise AssertionError("expected ValueError")
    assert push_argument(items, 5) == 5
    set_last(6)
    assert items == [1, 2, 3, 4, 6]
    alias = items
    extend(7)
    repeat(2)
    assert alias is items and items == [1, 2, 3, 4, 6, 7] * 2
    assert local_shadow(9) == [9] and len(items) == 12
    print("Mutable globals: aliases, rebinding, arguments, and exceptional writes verified")


if __name__ == "__main__":
    main()
