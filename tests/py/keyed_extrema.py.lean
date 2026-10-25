import «.formalsw».tests.py.«keyed_extrema.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.keyed_extrema
open FormalSW.PyAst
private abbrev program := KeyedExtremaAst.module

theorem absolute.result (n : Int) :
    Calls.ReturnsValue program "absolute" [.int n] (.int n.natAbs) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  exact Calls.Evaluates.builtin (.cons (Calls.Evaluates.lookup rfl) .nil) rfl

theorem absolute.«Returns» (n : Int) : (Calls.function program "absolute" [.int n]).Returns :=
  (absolute.result n).returns

open HeapCalls
private theorem list_result (arguments : Evaluates.Arguments program env expressions heap values finalHeap) :
    Evaluates program env (.list expressions) heap (.ref finalHeap.length) (finalHeap ++ [.list values]) := by
  intro anchors stack
  refine Reaches.next (following := argumentsState .list env [] expressions stack heap) rfl ?_
  apply (Evaluates.arguments_reach arguments .list [] anchors stack).trans
  exact .next (by simp [step, result, run, primitive, Mutable.allocate, Except.map]) .refl

/-- Equal absolute-value keys retain the first original item, including negative inputs. -/
theorem first_tie.result (n : Int) (heap : Mutable.Heap) :
    ReturnsValue program "first_tie" [.scalar (.int n)] heap (.scalar (.int n))
      (heap ++ [.list [.scalar (.int n), .scalar (.int (-n))]]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.extremum_sequence (items := [.scalar (.int n), .scalar (.int (-n))])
    (list_result (.cons (Evaluates.lookup rfl) (.cons
      (Evaluates.unary (Evaluates.lookup rfl) rfl) .nil)))
  · simp [Mutable.sequence]
  · apply ExtremumReturns.next (candidate := .scalar (.int n)) (score := .scalar (.int n.natAbs))
      (afterKey := heap ++ [.list [.scalar (.int n), .scalar (.int (-n))]])
      (afterSelection := heap ++ [.list [.scalar (.int n), .scalar (.int (-n))]])
      (updated := (.scalar (.int n), .scalar (.int n.natAbs)))
    · simp [extremumItem, Mutable.sequence]
    · apply Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil)
      rfl
    · rfl
    · apply ExtremumReturns.next (candidate := .scalar (.int (-n))) (score := .scalar (.int n.natAbs))
        (afterKey := heap ++ [.list [.scalar (.int n), .scalar (.int (-n))]])
        (afterSelection := heap ++ [.list [.scalar (.int n), .scalar (.int (-n))]])
        (updated := (.scalar (.int n), .scalar (.int n.natAbs)))
      · simp [extremumItem, Mutable.sequence]
      · apply Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil)
        simp [primitive, scalarResult, Calls.absoluteValue]
      · simp [SequenceExtremum.choose, HeapCalls.compare, scalarCompare, evalCmpOp, Mutable.truth, scalarTruth, Except.map]
      · apply ExtremumReturns.done
        simp [extremumItem, Mutable.sequence]

theorem first_tie.«Returns» (n : Int) : (HeapCalls.scalarFunction program "first_tie" [.int n]).Returns :=
  ReturnsValue.scalar_returns (first_tie.result n [])

theorem first_tie.«Supported» (n : Int) : (HeapCalls.scalarFunction program "first_tie" [.int n]).Supported :=
  (first_tie.«Returns» n).supported

end tests.py.keyed_extrema
