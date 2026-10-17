"""Run: python3 tests/py/object_equivalence.py (or ./test).

Python's overridable == and stored-state equivalence answer different questions.
The matching Lean examples are in object_equivalence.lean.
"""

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from lang.py.object_snapshot import equivalent, equivalent_roots


class Node:
    def __init__(self, value):
        self.value = value
        self.next = None

    def __eq__(self, other):
        raise AssertionError("equivalence must not invoke user equality")


def main():
    left = Node(7)
    right = Node(7)
    left.next = left
    right.next = right
    assert equivalent(left, right)  # Equal state despite different allocations.
    right.value = 8
    assert not equivalent(left, right)

    shared = []
    assert not equivalent([shared, shared], [[], []])
    assert not equivalent(1, True)
    assert equivalent(10**100, 10**100)

    # Return value alone misses whether the function copied its argument.
    argument_left = [1]
    argument_right = [1]
    copied_result = [1]
    assert equivalent(argument_left, copied_result)
    assert not equivalent_roots(
        [argument_left, argument_left], [copied_result, argument_right]
    )
    print("Object equivalence: cycles, attributes, aliases, and scalar types checked")


if __name__ == "__main__":
    main()
