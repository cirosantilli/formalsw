import «.formalsw».tests.py.«isinstance_int.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.isinstance_int
open FormalSW.PyAst
private abbrev program := IsinstanceIntAst.module

/-- The actual source performs the modeled type test for every scalar input. -/
theorem integer.result (value : Constant) :
    Calls.ReturnsValue program "integer" [value] (.bool (Calls.isInteger value)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  exact Calls.Evaluates.builtin (.cons (Calls.Evaluates.lookup rfl) .nil) rfl

theorem integer.«Returns» (value : Int) : (Calls.function program "integer" [.int value]).Returns :=
  (integer.result (.int value)).returns

theorem integer.«Supported» (value : Int) : (Calls.function program "integer" [.int value]).Supported :=
  (integer.«Returns» value).supported

/-- Inspecting a list's type neither traverses nor mutates its contents. -/
theorem sequence.result (heap : Mutable.Heap) (address : Nat) :
    HeapCalls.ReturnsValue program "sequence" [.ref address] heap (.scalar (.bool false)) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup rfl) .nil) rfl

theorem sequence.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (_typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "sequence" [.ref address] heap).Returns :=
  (sequence.result heap address).returns

theorem sequence.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "sequence" [.ref address] heap).Supported :=
  (sequence.«Returns» heap address valid typed).supported

end tests.py.isinstance_int
