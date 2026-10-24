def increased(n: int) -> int:
    """
    @formalsw: Returns
    """
    items = [n]
    items[0] += 1
    return items[0]


def receiver(items: list[int], log: list[int]) -> list[int]:
    log.append(1)
    return items


def index(log: list[int]) -> int:
    log.append(2)
    return 0


def right(items: list[int], log: list[int]) -> int:
    log.append(3)
    items[0] = 100
    return 4


def ordered(items: list[int], log: list[int]) -> int:
    receiver(items, log)[index(log)] += right(items, log)
    return items[0]


def append_right(items: list[int]) -> int:
    items.append(99)
    return 4


def negative_index(items: list[int]) -> int:
    items[-1] += append_right(items)
    return items[-1]


def failing_rhs(items: list[int], log: list[int]) -> int:
    items[0] += 1 // 0
    return items[0]


def dictionary(items: dict[int, int], key: int, log: list[int]) -> int:
    items[key] += index(log)
    return items[key]


def tuple_failure(n: int) -> int:
    items = ([n],)
    items[0] += [n + 1]
    return n
