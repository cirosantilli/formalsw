import «.formalsw».tests.py.«divmod.py.ast»
import FormalSW

namespace tests.py.divmod
open FormalSW.PyAst
private abbrev program := DivmodAst.module

/-- The proof covers every signed pair, preserving all preexisting heap objects. -/
theorem recombine.result (n d : Int) (nonzero : d ≠ 0) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "recombine" [.scalar (.int n), .scalar (.int d)] heap
      (.scalar (.int n)) (heap ++
        [.tuple [.scalar (.int (n.fdiv d)), .scalar (.int (n - d * n.fdiv d))]]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.unpack
    (items := [.scalar (.int (n.fdiv d)), .scalar (.int (n - d * n.fdiv d))])
    (afterUnpack := heap ++ [.tuple [.scalar (.int (n.fdiv d)), .scalar (.int (n - d * n.fdiv d))]]) rfl
  · apply HeapCalls.Evaluates.builtin
      (.cons (HeapCalls.Evaluates.lookup rfl) (.cons (HeapCalls.Evaluates.lookup rfl) .nil))
    exact Mutable.divmod_ints n d nonzero heap
  · simp [Mutable.sequence]
  · rfl
  · apply HeapCalls.BlockReturns.return_value
    apply HeapCalls.Evaluates.binary
      (HeapCalls.Evaluates.binary (value := .scalar (.int (n.fdiv d * d)))
        (HeapCalls.Evaluates.lookup rfl) (HeapCalls.Evaluates.lookup rfl) rfl)
      (HeapCalls.Evaluates.lookup rfl)
    simp [Mutable.binary, scalarBinary, Int.mul_comm]
    omega

private theorem original.result (n d : Int) :
    Finishes (scalarFunction program "original" [.int n, .int d]).step
      (scalarFunction program "original" [.int n, .int d]).initial (.ok (.int n)) :=
  Execution.finishes_of_observe (fuel := 2) rfl

theorem recombine.«Returns» (n d : Int) (condition : Calls.Condition program
    (fun name => if name = "d" then some (.int d) else none) DivmodAst.requires_recombine_0) :
    (HeapCalls.scalarFunction program "recombine" [.int n, .int d]).Returns := by
  have nonzero : d ≠ 0 := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  exact (recombine.result n d nonzero []).scalar_returns

theorem recombine.«Equiv(original)» (n d : Int) (condition : Calls.Condition program
    (fun name => if name = "d" then some (.int d) else none) DivmodAst.requires_recombine_0) :
    (HeapCalls.scalarFunction program "recombine" [.int n, .int d]).Equiv
      (scalarFunction program "original" [.int n, .int d]) := by
  have nonzero : d ≠ 0 := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  have left := HeapCalls.ReturnsValue.scalar_finishes (values := [.int n, .int d])
    (recombine.result n d nonzero [])
  have right := original.result n d
  intro outcome
  constructor
  · intro run
    rw [run.unique left]
    exact right
  · intro run
    rw [run.unique right]
    exact left

theorem recombine.«Supported» :
    (∀ n d : Int, Calls.Condition program
      (fun name => if name = "d" then some (.int d) else none) DivmodAst.requires_recombine_0 →
      (HeapCalls.scalarFunction program "recombine" [.int n, .int d]).Supported) ∧
    (∀ n d : Int, Calls.Condition program
      (fun name => if name = "d" then some (.int d) else none) DivmodAst.requires_recombine_0 →
      (scalarFunction program "original" [.int n, .int d]).Supported) :=
  ⟨fun n d h => (recombine.«Returns» n d h).supported,
    fun n d _ => Execution.supported_of_finishes (original.result n d)⟩

end tests.py.divmod
