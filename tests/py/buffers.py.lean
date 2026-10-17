import «.formalsw».tests.py.«buffers.py.ast»
import FormalSW

namespace tests.py.buffers
open FormalSW.PyAst
private abbrev program := BuffersAst.module

/-- Allocation and repetition create distinct buffers for every integer count. -/
theorem flags.result (n : Int) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "flags" [.scalar (.int n)] heap (.ref (heap.length + 1))
      (heap ++ [.bytearray [1]] ++ [.bytearray (List.replicate n.toNat 1)]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.binary
    (av := .ref heap.length) (middle := heap ++ [.bytearray [1]])
    (bv := .scalar (.int n)) (afterRight := heap ++ [.bytearray [1]])
  · apply HeapCalls.Evaluates.builtin (.cons HeapCalls.Evaluates.constant .nil)
    rfl
  · exact HeapCalls.Evaluates.lookup rfl
  · simp [Mutable.binary, Mutable.allocateBuffer, Except.map, show (BinOp.mult == .mult) = true from rfl]

theorem flags.«Returns» (n : Int) :
    (HeapCalls.call program "flags" [.scalar (.int n)] []).Returns :=
  (flags.result n []).returns

theorem flags.«Supported» (n : Int) :
    (HeapCalls.call program "flags" [.scalar (.int n)] []).Supported :=
  (flags.«Returns» n).supported

/-- The first sieve slot is cleared without changing its address. -/
theorem first_zero.result (n : Nat) (positive : 0 < n) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "first_zero" [.scalar (.int n)] heap (.ref (heap.length + 1))
      (heap ++ [.bytearray [1]] ++ [.bytearray ((List.replicate n 1).set 0 0)]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign
  · exact HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup rfl) .nil) (flags.result n heap)
  · apply HeapCalls.BlockReturns.setItem
      (afterWrite := heap ++ [.bytearray [1]] ++ [.bytearray ((List.replicate n 1).set 0 0)])
    · intros; simp
    · exact HeapCalls.Evaluates.constant
    · exact .cons (HeapCalls.Evaluates.lookup rfl) (.cons HeapCalls.Evaluates.constant .nil)
    · have found : (heap ++ [.bytearray [1]] ++ [.bytearray (List.replicate n 1)])[heap.length + 1]? =
          some (Mutable.Object.bytearray (List.replicate n 1)) := by simp
      have write := Mutable.setItem_buffer _ (heap.length + 1) 0 (List.replicate n 1) 0 found
        (by simpa using positive)
      simpa using write
    · exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

theorem first_zero.«Returns» (n : Int)
    (requires : Calls.Condition program (fun name => if name = "n" then some (.int n) else none)
      BuffersAst.requires_first_zero_0) :
    (HeapCalls.call program "first_zero" [.scalar (.int n)] []).Returns := by
  have positive := Calls.Evaluates.condition_int_compare requires (by rfl)
  simp [evalCmpOp] at positive
  have natural : (n.toNat : Int) = n := Int.toNat_of_nonneg (by omega)
  simpa [natural] using (first_zero.result n.toNat (by omega) []).returns

theorem first_zero.«Supported» (n : Int)
    (requires : Calls.Condition program (fun name => if name = "n" then some (.int n) else none)
      BuffersAst.requires_first_zero_0) :
    (HeapCalls.call program "first_zero" [.scalar (.int n)] []).Supported :=
  (first_zero.«Returns» n requires).supported

/-- Reads compose with a helper that allocates a fresh buffer. -/
theorem first_flag.result (n : Nat) (positive : 0 < n) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "first_flag" [.scalar (.int n)] heap (.scalar (.int 1))
      (heap ++ [.bytearray [1]] ++ [.bytearray (List.replicate n 1)]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.subscript (value := .ref (heap.length + 1)) (position := .scalar (.int 0))
    (middle := heap ++ [.bytearray [1]] ++ [.bytearray (List.replicate n 1)])
    (afterIndex := heap ++ [.bytearray [1]] ++ [.bytearray (List.replicate n 1)])
  · intro a b c impossible; cases impossible
  · exact HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup rfl) .nil) (flags.result n heap)
  · exact HeapCalls.Evaluates.constant
  · have read := Mutable.getItem_buffer
      (heap ++ [.bytearray [1]] ++ [.bytearray (List.replicate n 1)]) (heap.length + 1) 0 (List.replicate n 1)
      (by simp) (by simpa using positive)
    simpa using read

theorem first_flag.«Returns» (n : Int)
    (requires : Calls.Condition program (fun name => if name = "n" then some (.int n) else none)
      BuffersAst.requires_first_flag_0) :
    (HeapCalls.scalarFunction program "first_flag" [.int n]).Returns := by
  have positive := Calls.Evaluates.condition_int_compare requires (by rfl)
  simp [evalCmpOp] at positive
  have natural : (n.toNat : Int) = n := Int.toNat_of_nonneg (by omega)
  have run := first_flag.result n.toNat (by omega) []
  rw [natural] at run
  exact run.scalar_returns

theorem first_flag.«Supported» (n : Int)
    (requires : Calls.Condition program (fun name => if name = "n" then some (.int n) else none)
      BuffersAst.requires_first_flag_0) :
    (HeapCalls.scalarFunction program "first_flag" [.int n]).Supported :=
  (first_flag.«Returns» n requires).supported

end tests.py.buffers
