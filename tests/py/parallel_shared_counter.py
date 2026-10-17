#!/usr/bin/env python3
"""A shared counter and the classic lost-update race.

Run: python3 tests/py/parallel_shared_counter.py
Prove: ./cleanxy tests/py/parallel_shared_counter.py

The counter is a one-element list so both workers share the same mutable integer.
Both workers also receive the SAME mutex. sleep(0) gives the other worker a
chance to run, making the unsafe version's lost update easy to see.
"""
from concurrent.futures import ThreadPoolExecutor
from threading import Lock
from time import sleep


def increment_unsafe(counter: list[int], mutex: Lock) -> None:
    """Increment using an unprotected read-modify-write operation.

    @cleanxy: Not Concurrent(run_trial)
    """
    snapshot = counter[0]
    sleep(0)
    counter[0] = snapshot + 1


def increment_safe(counter: list[int], mutex: Lock) -> None:
    """Hold the shared mutex for the whole read-modify-write operation.

    @cleanxy: Concurrent(run_trial)
    """
    mutex.acquire()
    snapshot = counter[0]
    sleep(0)
    counter[0] = snapshot + 1
    mutex.release()


def run_trial(increment):
    counter = [0]
    mutex = Lock()
    with ThreadPoolExecutor(max_workers=2) as workers:
        futures = [workers.submit(increment, counter, mutex) for _ in range(2)]
        # Propagate worker exceptions; joining alone would hide them.
        for future in futures:
            future.result()
    assert counter[0] == 2, f"expected counter == 2 after two increments; got {counter[0]}"


def main():
    trials = 20
    print("Shared counter: two workers each increment once, starting at zero.\n")
    for increment in (increment_unsafe, increment_safe):
        failures = 0
        print(f"{increment.__name__}: {trials} real-thread trials")
        for trial in range(1, trials + 1):
            try:
                run_trial(increment)
            except AssertionError as error:
                failures += 1
                if increment is increment_safe:
                    raise
                if failures <= 3:
                    print(f"  Trial {trial}: AssertionError: {error}")
        print(f"  Lost updates: {failures}/{trials} ({failures / trials:.0%})\n")
        if increment is increment_unsafe and failures == 0:
            print("  No unlucky schedule this time; rerun to try again.\n")
    print("The unsafe assertions above are caught so both versions can run.")
    print("The Lean proof checks every modeled schedule, not just these trials.")


if __name__ == "__main__":
    main()
