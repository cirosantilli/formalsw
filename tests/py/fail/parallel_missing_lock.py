from threading import Lock
from time import sleep


def increment(counter: list[int], mutex: Lock) -> None:
    """The claimed guarantee is false without synchronization.

    @formalsw: theorem preserves_both_updates :
      Ensures(Parallel(List.replicate 2 (this_function [.ref 0, .lock 0]),
        { objects := [.array [.int 0]] }), fun state => state.item 0 0 = some (.int 2))
    """
    snapshot = counter[0]
    sleep(0)
    counter[0] = snapshot + 1
