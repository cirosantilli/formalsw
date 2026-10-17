#!/usr/bin/env python3
"""Executable smoke tests for the plain-Python builtin models."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
MODEL_ROOT = ROOT / "lang/py/builtin/type"


def load(name: str):
    path = MODEL_ROOT / f"{name}.py"
    spec = importlib.util.spec_from_file_location(f"formalsw_builtin_{name}", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_path(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> None:
    bool_type = load("bool").bool
    assert int(bool_type(0)) == 0
    assert int(bool_type(7)) == 1
    assert not bool_type(0) and bool_type(-1)

    tuple_model = load("tuple").tuple([1, 2])
    assert len(tuple_model) == 2 and tuple_model[1] == 2

    bytes_model = load("bytes").bytes([0, 255])
    assert len(bytes_model) == 2 and bytes_model[1] == 255

    bytearray_model = load("bytearray").bytearray([1, 2])
    bytearray_model.append(3)
    bytearray_model.reverse()
    assert bytearray_model.value == [3, 2, 1]

    range_type = load("range").range
    positive = range_type(1, 8, 2)
    negative = range_type(5, -1, -2)
    assert len(positive) == 4 and positive[-1] == 7 and 5 in positive
    assert len(negative) == 3 and negative[2] == 1 and 2 not in negative

    iterator_model = load("iterator").iterator([4, 5])
    assert iter(iterator_model) is iterator_model
    assert next(iterator_model) == 4 and next(iterator_model) == 5
    try:
        next(iterator_model)
    except StopIteration:
        pass
    else:
        raise AssertionError("iterator did not raise StopIteration")

    functions = load_path(
        "formalsw_builtin_functions",
        ROOT / "lang/py/builtin/function.py",
    )
    assert functions.bin(-10) == [45, 48, 98, 49, 48, 49, 48]
    assert functions.hex(255) == [48, 120, 102, 102]
    assert functions.abs(-7) == 7
    assert functions.sum([1, 2, 3], 4) == 10
    assert functions.round(25, -1) == 20
    assert functions.sorted([3, 1, 2]) == [1, 2, 3]
    assert list(functions.zip([1, 2], [3, 4])) == [(1, 3), (2, 4)]


if __name__ == "__main__":
    main()
