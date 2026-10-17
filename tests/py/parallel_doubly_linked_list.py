#!/usr/bin/env python3
"""Concurrent insertion in a doubly linked list can corrupt its links.

Run: python3 tests/py/parallel_doubly_linked_list.py
Prove: ./cleanxy tests/py/parallel_doubly_linked_list.py

HEAD <-> TAIL starts empty. Two workers insert distinct, preallocated nodes
immediately after HEAD. Each worker receives the same mutex.
"""
from concurrent.futures import ThreadPoolExecutor
from threading import Barrier, Lock
from time import sleep


class Node:
    def __init__(self):
        self.prev = None
        self.next = None


def insert_unsafe(head: Node, node: Node, mutex: Lock) -> None:
    """Concurrent inserts can leave next and prev disagreeing.

    @cleanxy: theorem can_corrupt_links :
      CanReturn(Parallel([
        this_function [.ref 0, .ref 2, .lock 0],
        this_function [.ref 0, .ref 3, .lock 0]], DoublyLinked.initial), DoublyLinked.broken)

    @cleanxy: theorem links_not_guaranteed :
      Not Ensures(Parallel([
        this_function [.ref 0, .ref 2, .lock 0],
        this_function [.ref 0, .ref 3, .lock 0]], DoublyLinked.initial), DoublyLinked.linksAgree)
    """
    following = head.next
    node.prev = head
    node.next = following
    sleep(0)
    head.next = node
    following.prev = node


def insert_safe(head: Node, node: Node, mutex: Lock) -> None:
    """The shared mutex protects the complete insertion, including its first read.

    @cleanxy: theorem preserves_list :
      Ensures(
        Parallel(
          [
            this_function [.ref 0, .ref 2, .lock 0],
            this_function [.ref 0, .ref 3, .lock 0]
          ],
          DoublyLinked.initial
        ),
        DoublyLinked.valid
      )
    """
    mutex.acquire()
    following = head.next
    node.prev = head
    node.next = following
    sleep(0)
    head.next = node
    following.prev = node
    mutex.release()


def run_trial(insert):
    head, tail, first_node, second_node = Node(), Node(), Node(), Node()
    head.next = tail
    tail.prev = head
    mutex = Lock()
    ready = Barrier(2)

    def worker(node):
        ready.wait(timeout=5)
        insert(head, node, mutex)

    with ThreadPoolExecutor(max_workers=2) as workers:
        first = workers.submit(worker, first_node)
        second = workers.submit(worker, second_node)
        first.result(timeout=5)
        second.result(timeout=5)

    # Every forward edge must have a matching backward edge, and vice versa.
    for node in (head, tail, first_node, second_node):
        if node.next is not None:
            assert node.next.prev is node, "corrupted link: node.next.prev is not node"
        if node.prev is not None:
            assert node.prev.next is node, "corrupted link: node.prev.next is not node"
    assert head.prev is None and tail.next is None, "sentinel links changed"
    # Neither a lost node nor a cycle counts as a valid list.
    seen = []
    current = head.next
    while current is not tail:
        assert current is not None and current not in seen, "broken chain or cycle"
        seen.append(current)
        current = current.next
    assert len(seen) == 2 and first_node in seen and second_node in seen, "an inserted node was lost"


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
