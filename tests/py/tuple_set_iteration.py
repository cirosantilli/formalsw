#!/usr/bin/env python3
"""
@formalsw: theorem count_result
  (choices : FormalSW.PyAst.ChoiceSchedule) (heap : FormalSW.PyAst.Mutable.Heap) (address : Nat)
  (items : List (FormalSW.PyAst.HashKey × FormalSW.PyAst.Mutable.Value)) :
  heap[address]? = some (.keySet items) →
  ((FormalSW.PyAst.SetCalls.call TupleSetIterationAst.module "count" [.ref address] heap).run choices).Finishes
    ⟨.ok (.scalar (.int items.length)), [], heap, heap.length⟩

@formalsw: theorem counts_equivalent
  (heap : FormalSW.PyAst.Mutable.Heap) (address : Nat)
  (items : List (FormalSW.PyAst.HashKey × FormalSW.PyAst.Mutable.Value)) :
  heap[address]? = some (.keySet items) →
  (FormalSW.PyAst.SetCalls.call TupleSetIterationAst.module "fast_count" [.ref address] heap).Equiv
    (FormalSW.PyAst.SetCalls.call TupleSetIterationAst.module "count" [.ref address] heap)
"""


def count(values: set[tuple[int, int]]) -> int:
    total = 0
    for value in values:
        total += 1
    return total


def fast_count(values: set[tuple[int, int]]) -> int:
    return len(values)
