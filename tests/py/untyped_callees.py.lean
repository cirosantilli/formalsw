import «.formalsw».tests.py.«untyped_callees.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.untyped_callees
open FormalSW.PyAst
private abbrev program := UntypedCalleesAst.module

private theorem identity_result (value : Constant) :
    Calls.ReturnsValue program "identity" [value] value := by
  apply Calls.BlockReturns.function rfl rfl
  exact Calls.BlockReturns.return_value (Calls.Evaluates.lookup rfl)

/-- The helper's missing annotation supplies no premise to this source execution proof. -/
theorem scalar_entry.result (value : Constant) :
    Calls.ReturnsValue program "scalar_entry" [value] value := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  exact Calls.Evaluates.call (.cons (Calls.Evaluates.lookup rfl) .nil) (identity_result value)

theorem scalar_entry.«Returns» (n : Int) : (Calls.function program "scalar_entry" [.int n]).Returns :=
  (scalar_entry.result (.int n)).returns

private theorem push_result (heap : Mutable.Heap) (address : Nat) (items : List Mutable.Value)
    (found : heap[address]? = some (.list items)) (value : Mutable.Value) :
    HeapCalls.ReturnsValue program "push" [.ref address, value] heap value
      (heap.set address (.list (items ++ [value]))) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.discard
  · exact HeapCalls.Evaluates.append (HeapCalls.Evaluates.lookup rfl) found
      (HeapCalls.Evaluates.lookup rfl) found
  · exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

/-- An untyped callee mutates the original referenced list and returns the exact supplied value. -/
theorem heap_entry.result (heap : Mutable.Heap) (address : Nat) (items : List Mutable.Value)
    (found : heap[address]? = some (.list items)) (value : Mutable.Value) :
    HeapCalls.ReturnsValue program "heap_entry" [.ref address, value] heap value
      (heap.set address (.list (items ++ [value]))) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.call
    (.cons (HeapCalls.Evaluates.lookup rfl) (.cons (HeapCalls.Evaluates.lookup rfl) .nil))
    (push_result heap address items found value)

theorem heap_entry.«Returns» (heap : Mutable.Heap) (address : Nat) (value : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "heap_entry" [.ref address, .scalar (.int value)] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (heap_entry.result heap address _ found (.scalar (.int value))).returns

theorem heap_entry.«Supported» (heap : Mutable.Heap) (address : Nat) (value : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "heap_entry" [.ref address, .scalar (.int value)] heap).Supported :=
  (heap_entry.«Returns» heap address value valid typed).supported

theorem guarded_entry.result (value : Constant) :
    Calls.ReturnsValue program "guarded_entry" [value] value := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  exact Calls.Evaluates.call (.cons (Calls.Evaluates.lookup rfl) .nil) (identity_result value)

/-- The predicate's untyped helper leaves the entry's exact Requires guard in place. -/
theorem guarded_entry.«Returns» (n : Int) (_requires : Calls.Condition program
    (fun name => if name = "n" then some (.int n) else none) UntypedCalleesAst.requires_guarded_entry_0) :
    (Calls.function program "guarded_entry" [.int n]).Returns :=
  (guarded_entry.result (.int n)).returns

end tests.py.untyped_callees
