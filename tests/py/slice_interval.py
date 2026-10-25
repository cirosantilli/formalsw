#!/usr/bin/env python3
"""
@formalsw: theorem window_result
  (values : List Int) (start stop : Nat) (heap : FormalSW.PyAst.Mutable.Heap) (address : Nat) :
  start ≤ stop → stop ≤ values.length →
  heap[address]? = some (.list (values.map (fun value => .scalar (.int value)))) →
  FormalSW.PyAst.HeapCalls.ReturnsValue SliceIntervalAst.module "window"
    [.ref address, .scalar (.int start), .scalar (.int stop)] heap (.ref heap.length)
    (heap ++ [.list (((values.drop start).take (stop - start)).map
      (fun value => .scalar (.int value)))])
"""


def window(values: list[int], start: int, stop: int) -> list[int]:
    return values[start:stop]


if __name__ == "__main__":
    assert window([1, 2, 3, 4], 1, 3) == [2, 3]
    assert window([], 0, 0) == []
