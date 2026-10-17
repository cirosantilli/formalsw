#!/usr/bin/env python3
"""A shared counter and the classic lost-update race.

Run: python3 tests/py/parallel_shared_counter.py
Prove: ./formalsw tests/py/parallel_shared_counter.py

The counter is the first element of a nonempty integer list. The proof covers
any initial contents and any nonnegative worker count; main demonstrates two workers.
Both workers also receive the SAME mutex. sleep(0) gives the other worker a
chance to run, making the unsafe version's lost update easy to see.
"""
from concurrent.futures import ThreadPoolExecutor
from threading import Lock
from time import sleep


def increment_unsafe(counter: list[int], mutex: Lock) -> None:
    """Increment using an unprotected read-modify-write operation.

    @formalsw: theorem loses_an_update :
      ∃ (counter worker_count : PyValue),
        py("valid_trial_input(counter, worker_count)") ∧
        Throws(py("run_trial(this_function, counter, worker_count)"))
    """
    snapshot = counter[0]
    sleep(0)
    counter[0] = snapshot + 1


def increment_safe(counter: list[int], mutex: Lock) -> None:
    """Hold the shared mutex for the whole read-modify-write operation.

    @formalsw: theorem preserves_updates :
      ∀ (counter worker_count : PyValue),
        py("valid_trial_input(counter, worker_count)") →
        Returns(py("run_trial(this_function, counter, worker_count)"))
    """
    mutex.acquire()
    snapshot = counter[0]
    sleep(0)
    counter[0] = snapshot + 1
    mutex.release()


def valid_trial_input(counter, worker_count):
    return (
        type(counter) == list
        and len(counter) > 0
        and all(type(item) == int for item in counter)
        and type(worker_count) == int
        and worker_count >= 0
    )


def run_trial(increment, counter: list[int], worker_count: int):
    assert valid_trial_input(counter, worker_count), "invalid trial input"
    before = counter.copy()
    mutex = Lock()
    with ThreadPoolExecutor(max_workers=max(1, worker_count)) as workers:
        futures = [workers.submit(increment, counter, mutex) for _ in range(worker_count)]
        # Propagate worker exceptions; joining alone would hide them.
        for future in futures:
            future.result()
    assert counter[0] == before[0] + worker_count, "an increment was lost"
    assert counter[1:] == before[1:], "another counter element changed"


def main():
    trials = 20
    print("Shared counter: two workers each increment once, starting at zero.\n")
    for increment in (increment_unsafe, increment_safe):
        failures = 0
        print(f"{increment.__name__}: {trials} real-thread trials")
        for trial in range(1, trials + 1):
            try:
                run_trial(increment, [0], 2)
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
