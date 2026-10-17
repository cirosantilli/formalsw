#!/usr/bin/env python3
"""Deadlock, livelock, and successful completion of joined worker batches.

Prove: ./formalsw tests/py/parallel_liveness.py
Run: python3 tests/py/parallel_liveness.py

The bad examples run in disposable child processes so the demonstration exits.
Timeouts are observations, not proofs; the Lean file supplies actual witnesses.
"""
from concurrent.futures import ThreadPoolExecutor
from multiprocessing import get_context
from threading import Lock
from time import sleep


def lock_pair(first: Lock, second: Lock) -> None:
    """Opposite acquisition orders can leave each worker waiting for the other.

    @formalsw: theorem opposite_order_can_deadlock :
      CanDeadlock(Parallel([this_function [.lock 0, .lock 1],
                            this_function [.lock 1, .lock 0]], {}))

    @formalsw: theorem opposite_order_not_halts :
      Not Halts(Parallel([this_function [.lock 0, .lock 1],
                          this_function [.lock 1, .lock 0]], {}))

    @formalsw: theorem same_order_returns :
      Returns(Parallel([this_function [.lock 0, .lock 1],
                        this_function [.lock 0, .lock 1]], {}))
    """
    first.acquire()
    sleep(0)
    second.acquire()
    second.release()
    first.release()


def retry_forever(mutex: Lock) -> None:
    """A broken retry protocol: release the lock and retry without doing work.

    Both workers can keep taking turns forever. Nobody needs to be starved.

    @formalsw: theorem can_livelock :
      CanDiverge(Parallel([this_function [.lock 0], this_function [.lock 0]], {}))

    @formalsw: theorem does_not_halt :
      Not Halts(Parallel([this_function [.lock 0], this_function [.lock 0]], {}))

    @formalsw: theorem quoted_can_livelock :
      CanDiverge(py("run_retries(this_function, 2)"))
    """
    while True:
        mutex.acquire()
        mutex.release()
        sleep(0)


def finish(mutex: Lock) -> None:
    """One complete lock region, unlike the broken retry protocol.

    @formalsw: theorem quoted_returns :
      Returns(py("run_retries(this_function, 2)"))

    @formalsw: theorem quoted_halts :
      Halts(py("run_retries(this_function, 2)"))

    @formalsw: theorem quoted_deadlock_free :
      DeadlockFree(py("run_retries(this_function, 2)"))
    """
    mutex.acquire()
    mutex.release()


def acquire_twice(mutex: Lock) -> None:
    """A Python Lock is not reentrant: even one worker can deadlock itself.

    @formalsw: theorem can_deadlock :
      CanDeadlock(py("run_retries(this_function, 1)"))
    """
    mutex.acquire()
    mutex.acquire()


def run_retries(worker, worker_count: int):
    assert type(worker_count) == int and worker_count >= 0
    mutex = Lock()
    with ThreadPoolExecutor(max_workers=max(1, worker_count)) as workers:
        futures = [workers.submit(worker, mutex) for _ in range(worker_count)]
        for future in futures:
            future.result()


def run_pair(opposite):
    first, second = Lock(), Lock()
    with ThreadPoolExecutor(max_workers=2) as workers:
        a = workers.submit(lock_pair, first, second)
        b = workers.submit(lock_pair, second, first) if opposite else workers.submit(lock_pair, first, second)
        a.result()
        b.result()


def main():
    run_pair(False)
    print("Consistent lock ordering: both workers completed.")
    for name, target, arguments in (
        ("Opposite lock ordering", run_pair, (True,)),
        ("Retry livelock", run_retries, (retry_forever, 2)),
    ):
        process = get_context("spawn").Process(target=target, args=arguments)
        process.start()
        process.join(0.5)
        if process.is_alive():
            print(f"{name}: still waiting after 0.5 s; stopping the demonstration.")
            process.terminate()
            process.join()
        else:
            assert process.exitcode == 0
            print(f"{name}: completed on this schedule; deadlock is possible, not inevitable.")
    print("The proofs establish deadlock and infinite-execution witnesses independently of these timeouts.")


if __name__ == "__main__":
    main()
