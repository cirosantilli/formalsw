import «.formalsw».tests.py.«memo_heap_calls.py.ast»
import lang.py.FormalSW.MemoHeapCalls
import lang.py.FormalSW.MemoCallRules

namespace tests.py.memo_heap_calls
open FormalSW.PyAst
private abbrev program := MemoHeapCallsAst.module
private def spec (key : MemoCalls.Key) (value : Constant) : Prop :=
  ∃ n : Int, key = ⟨"double", [n]⟩ ∧ value = .int (n + n)

private theorem double_result (n : Int) :
    MemoCalls.ReturnsValue program program.memoizedFunctions spec "double" [.int n] (.int (n + n)) := by
  apply MemoCalls.BlockReturns.memoized_function (values := [n]) (by decide) rfl rfl
  · apply MemoCalls.BlockReturns.return_value
    exact MemoCalls.Evaluates.binary (MemoCalls.Evaluates.lookup rfl) (MemoCalls.Evaluates.lookup rfl) rfl
  · exact ⟨n, rfl, rfl⟩
  · rintro other ⟨k, same, rfl⟩
    have equal : n = k := by simpa [MemoCalls.Key.mk.injEq] using same
    simp [equal]

theorem double.«Returns» (n : Int) :
    (MemoCalls.sourceFunction program "double" [.int n]).Returns := (double_result n).returns

theorem double.«Supported» (n : Int) :
    (MemoCalls.sourceFunction program "double" [.int n]).Supported := (double.«Returns» n).supported

open FormalSW.PyAst.MemoHeapCalls

private theorem list_result (arguments : Evaluates.Arguments program spec env expressions heap values finalHeap) :
    Evaluates program spec env (.list expressions) heap (.ref finalHeap.length) (finalHeap ++ [.list values]) := by
  intro anchors stack
  refine Runs.next (following := HeapCalls.argumentsState .list env [] expressions stack heap) trivial rfl ?_
  apply (Evaluates.arguments_reach arguments .list [] anchors stack).trans
  exact Runs.next trivial (by simp [HeapCalls.step, HeapCalls.result, HeapCalls.run,
    HeapCalls.primitive, Mutable.allocate, Except.map]) .refl

private theorem call_double (n : Int) (env : Mutable.Env) (heap : Mutable.Heap)
    (found : env "n" = some (.scalar (.int n))) :
    Evaluates program spec env (.call (.name "double") [.name "n"]) heap (.scalar (.int (n + n))) heap :=
  Evaluates.call (.cons (Evaluates.lookup found) .nil)
    (ReturnsValue.memoized (by decide) (double_result n))

/-- Both source calls share the cache while the intervening list allocation retains its heap effect. -/
theorem caller.result (n : Int) :
    ReturnsValue program spec "caller" [.scalar (.int n)] [] (.scalar (.int (n + n + 1)))
      [.list [.scalar (.int (n + n))]] := by
  apply BlockReturns.function (by decide) rfl rfl
  apply BlockReturns.assign (list_result (.cons (call_double n _ [] rfl) .nil))
  apply BlockReturns.return_value
  apply Evaluates.binary (call_double n _ _ rfl)
  · exact Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil) rfl
  · rfl

private theorem condition_result (n : Int) :
    Evaluates program spec (fun key => if key = "n" then some (.scalar (.int n)) else none)
      MemoHeapCallsAst.requires_caller_0 [] (.scalar (.bool true)) [.list [.scalar (.int (n + n))]] := by
  apply Evaluates.compare
  · exact Evaluates.builtin (.cons (list_result (.cons (call_double n _ [] rfl) .nil)) .nil) rfl
  · exact Evaluates.constant
  · rfl

theorem requires_caller_0_supported (n : Int) :
    (MemoHeapCalls.evaluate program (fun key => if key = "n" then some (.scalar (.int n)) else none)
      MemoHeapCallsAst.requires_caller_0 []).Supported :=
  Execution.supported_of_finishes (condition_result n).finishes

theorem caller.«Returns» (n : Int)
    (_ : MemoHeapCalls.Condition program (fun key => if key = "n" then some (.scalar (.int n)) else none)
      MemoHeapCallsAst.requires_caller_0 []) :
    (MemoHeapCalls.scalarFunction program "caller" [.int n]).Returns := (caller.result n).scalar_returns

theorem caller.«Supported» (n : Int)
    (requires : MemoHeapCalls.Condition program (fun key => if key = "n" then some (.scalar (.int n)) else none)
      MemoHeapCallsAst.requires_caller_0 []) :
    (MemoHeapCalls.scalarFunction program "caller" [.int n]).Supported := (caller.«Returns» n requires).supported

end tests.py.memo_heap_calls
