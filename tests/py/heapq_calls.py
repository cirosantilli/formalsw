import heapq


def solve(n: int) -> int:
    """
    @formalsw: Equiv(reference)
    @formalsw: Returns
    """
    heap = []
    heapq.heappush(heap, n)
    heapq.heapify(heap)
    return heapq.heappop(heap)


def reference(n: int) -> int:
    return n
