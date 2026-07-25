#!/usr/bin/env python3


def merge_sort_int(values: list[int]) -> list[int]:
    """
    @cleanxy: Equiv(quick_sort_int)
    @cleanxy: BigO(n * (Nat.log2 n + 1), n = len(values))
    """
    if len(values) <= 1:
        return values
    middle = len(values) // 2
    left = merge_sort_int(values[:middle])
    right = merge_sort_int(values[middle:])
    merged = []
    left_index = 0
    right_index = 0
    while left_index < len(left) and right_index < len(right):
        if left[left_index] <= right[right_index]:
            merged += [left[left_index]]
            left_index += 1
        else:
            merged += [right[right_index]]
            right_index += 1
    return merged + left[left_index:] + right[right_index:]


def quick_sort_int(values: list[int]) -> list[int]:
    """@cleanxy: BigO(n * n, n = len(values))"""
    if len(values) <= 1:
        return values
    pivot = values[0]
    less = []
    equal = []
    greater = []
    for value in values:
        if value < pivot:
            less += [value]
        else:
            if value > pivot:
                greater += [value]
            else:
                equal += [value]
    return quick_sort_int(less) + equal + quick_sort_int(greater)


def merge_sort_untyped(values: list) -> list:
    """
    @cleanxy: Throws
    @cleanxy: EquivReturn(quick_sort)
    @cleanxy: BigO(n * (Nat.log2 n + 1), n = len(values))
    """
    if len(values) <= 1:
        return values
    middle = len(values) // 2
    left = merge_sort_untyped(values[:middle])
    right = merge_sort_untyped(values[middle:])
    merged = []
    left_index = 0
    right_index = 0
    while left_index < len(left) and right_index < len(right):
        if left[left_index] <= right[right_index]:
            merged += [left[left_index]]
            left_index += 1
        else:
            merged += [right[right_index]]
            right_index += 1
    return merged + left[left_index:] + right[right_index:]


def quick_sort(values: list) -> list:
    """@cleanxy: BigO(n * n, n = len(values))"""
    if len(values) <= 1:
        return values
    pivot = values[0]
    less = []
    equal = []
    greater = []
    for value in values:
        if value < pivot:
            less += [value]
        else:
            if value > pivot:
                greater += [value]
            else:
                equal += [value]
    return quick_sort(less) + equal + quick_sort(greater)
