#!/usr/bin/env python3
"""Concurrent insertion in a doubly linked list can corrupt its links.

Run: python3 tests/py/parallel_doubly_linked_list.py
Prove: ./formalsw tests/py/parallel_doubly_linked_list.py

The proof covers any existing list and any finite number of fresh insertions.
The executable demonstrates the race with two workers and an initially empty
HEAD <-> TAIL list. Each worker receives the same mutex.
"""
from concurrent.futures import ThreadPoolExecutor
from threading import Lock
from time import sleep


class Node:
    def __init__(self):
        self.prev = None
        self.next = None


def insert_unsafe(head: Node, node: Node, mutex: Lock) -> None:
    """Concurrent inserts can leave next and prev disagreeing.

    @formalsw: Not Concurrent(run_trial)
    """
    following = head.next
    node.prev = head
    node.next = following
    sleep(0)
    head.next = node
    following.prev = node


def insert_safe(head: Node, node: Node, mutex: Lock) -> None:
    """Every run_trial input and scheduling order must pass its assertions.

    @formalsw: Concurrent(run_trial)
    """
    mutex.acquire()
    following = head.next
    node.prev = head
    node.next = following
    sleep(0)
    head.next = node
    following.prev = node
    mutex.release()


def run_trial(insert, existing_count: int = 0, insertion_count: int = 2):
    head, tail = Node(), Node()
    existing = [Node() for _ in range(existing_count)]
    inserted = [Node() for _ in range(insertion_count)]
    chain = [head, *existing, tail]
    for left, right in zip(chain, chain[1:]):
        left.next = right
        right.prev = left
    mutex = Lock()
    with ThreadPoolExecutor(max_workers=max(1, len(inserted))) as workers:
        futures = [workers.submit(insert, head, node, mutex) for node in inserted]
        for future in futures:
            future.result()

    # Walk one step for each inserted node. Check membership and backlinks.
    current = head
    for _ in inserted:
        following = current.next
        assert following in inserted, "an inserted node was lost"
        assert following.prev is current, "corrupted link: next.prev is not current"
        current = following
    # The original nodes must still follow in their original order.
    for node in [*existing, tail]:
        assert current.next is node, "the original chain changed"
        assert node.prev is current, "corrupted link: prev is not current"
        current = node
    assert head.prev is None, "head sentinel changed"
    assert tail.next is None, "tail sentinel changed"


def main():
    print("Doubly linked list: two concurrent inserts after the same head.\n")
    for insert in (insert_unsafe, insert_safe):
        failures = 0
        print(f"{insert.__name__}: 20 real-thread trials")
        for trial in range(1, 21):
            try:
                run_trial(insert)
            except AssertionError as error:
                if insert is insert_safe:
                    raise
                failures += 1
                if failures <= 3:
                    print(f"  Trial {trial}: AssertionError: {error}")
        print(f"  Corrupted lists: {failures}/20 ({failures / 20:.0%})\n")
    print("Unsafe assertions are caught so both versions run; synchronized failures propagate.")


if __name__ == "__main__":
    main()
