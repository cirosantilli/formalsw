import «.formalsw».tests.py.«augmented_items.py.ast»
import FormalSW

namespace tests.py.augmented_items
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := AugmentedItemsAst.module

/-- The saved subscription is updated for every integer, without a fuel bound. -/
theorem increased.«Returns» (n : Int) : (HeapCalls.scalarFunction program "increased" [.int n]).Returns := by
  apply ReturnsValue.scalar_returns (heap := [.list [.scalar (.int (n + 1))]]) (value := .int (n + 1))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (Evaluates.list (.cons (Evaluates.lookup rfl) .nil))
  apply BlockContinues.returns (middleHeap := [.list [.scalar (.int (n + 1))]]) (body := [.augAssign (.subscript (.name "items") (.constant (.int 0))) .add (.constant (.int 1))])
  · apply BlockContinues.augItem (target := .ref 0) (key := .scalar (.int 0))
      (previous := .scalar (.int n)) (right := .scalar (.int 1)) (updated := .scalar (.int (n + 1)))
      (afterRead := [.list [.scalar (.int n)]]) (afterOperation := [.list [.scalar (.int n)]])
      (by intro a b c; simp) (Evaluates.lookup rfl) Evaluates.constant
    · simp [Mutable.getItem, Mutable.index, Except.map]
    · exact Evaluates.constant
    · simp [inplace, Mutable.binary, scalarBinary]
    · simp [Mutable.setItem, Mutable.index, Except.map]
  · apply BlockReturns.return_value
    apply Evaluates.subscript (by intro a b c; simp) (Evaluates.lookup rfl) Evaluates.constant
    simp [Mutable.getItem, Mutable.index, Except.map]

theorem increased.«Supported» (n : Int) : (HeapCalls.scalarFunction program "increased" [.int n]).Supported :=
  (increased.«Returns» n).supported

end tests.py.augmented_items
