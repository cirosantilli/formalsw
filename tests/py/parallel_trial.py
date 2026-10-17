"""A small regression example: trials also work without a linked list."""
from concurrent.futures import ThreadPoolExecutor
from threading import Lock


class Cell:
    def __init__(self):
        self.value = None


def mark(item: Cell, mutex: Lock):
    """Make each cell refer to itself.

    @formalsw: Concurrent(check_marks)
    """
    mutex.acquire()
    item.value = item
    mutex.release()


def check_marks(worker, count: int = 3):
    items = [Cell() for _ in range(count)]
    mutex = Lock()
    with ThreadPoolExecutor(max_workers=max(1, len(items))) as pool:
        futures = [pool.submit(worker, item, mutex) for item in items]
        for future in futures:
            future.result()
    for item in items:
        assert item.value is item


if __name__ == "__main__":
    check_marks(mark)
