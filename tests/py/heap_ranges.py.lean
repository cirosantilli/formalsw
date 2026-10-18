import «.formalsw».tests.py.«heap_ranges.py.ast»
import FormalSW

namespace tests.py.heap_ranges
open FormalSW.PyAst
private abbrev program := HeapRangesAst.module

private def body : List Stmt :=
  [.expr (.call (.attribute (.name "items") "append") [.name "k"])]

private def encode (values : List Nat) : List Mutable.Value :=
  values.map (fun (n : Nat) => .scalar (.int (n : Int)))

/-- Every iteration preserves the caller's existing objects and appends exactly
the current range index to the newly allocated list. -/
private theorem loop_continues (remaining start stop : Nat) (bound : stop = start + remaining)
    (env : Mutable.Env) (prior : Mutable.Heap) (acc : List Mutable.Value)
    (items : env "items" = some (.ref prior.length)) :
    ∃ finalEnv,
      HeapCalls.BlockContinues program env [.rangeStepLoop "k" start stop 1 body []]
        (prior ++ [acc]) finalEnv (prior ++ [acc ++ encode (List.range' start remaining)]) ∧
      finalEnv "items" = some (.ref prior.length) := by
  induction remaining generalizing start env acc with
  | zero =>
      simp only [List.range'_zero, encode, List.map_nil, List.append_nil]
      exact ⟨env, HeapCalls.BlockContinues.range_done
        (by simp [Calls.rangeContinues, bound]) HeapCalls.BlockContinues.nil, items⟩
  | succ remaining ih =>
      obtain ⟨finalEnv, recurse, finalItems⟩ := ih (start + 1) (by omega)
        (HeapCalls.setLocal env "k" (.scalar (.int start)))
        (acc ++ [.scalar (.int start)]) (by simpa [HeapCalls.setLocal] using items)
      refine ⟨finalEnv, HeapCalls.BlockContinues.range_step
        (by simp [Calls.rangeContinues]; omega) ?_, finalItems⟩
      apply HeapCalls.BlockContinues.append (body := body)
      · apply HeapCalls.BlockContinues.discard
        apply HeapCalls.Evaluates.append
          (HeapCalls.Evaluates.lookup (by simpa [HeapCalls.setLocal] using items))
          (old := acc) (current := acc) (afterItem := prior ++ [acc]) (by simp)
          (value := .scalar (.int (start : Int)))
          (HeapCalls.Evaluates.lookup (by simp [HeapCalls.setLocal]))
        simp
      · have update : (prior ++ [acc]).set prior.length (acc ++ [.scalar (.int (start : Int))]) =
            prior ++ [acc ++ [.scalar (.int (start : Int))]] := by simp
        rw [update]
        simpa [Calls.loopContinuation, body, List.range'_succ, encode, List.append_assoc,
          Int.natCast_add] using recurse

private theorem loop_result (remaining start stop : Nat) (bound : stop = start + remaining)
    (env : Mutable.Env) (prior : Mutable.Heap) (acc : List Mutable.Value)
    (items : env "items" = some (.ref prior.length)) :
    HeapCalls.BlockReturns program env
      [.rangeStepLoop "k" start stop 1 body [], .return (.name "items")]
      (prior ++ [acc]) (.ref prior.length)
      (prior ++ [acc ++ encode (List.range' start remaining)]) := by
  obtain ⟨finalEnv, executed, finalItems⟩ := loop_continues remaining start stop bound env prior acc items
  exact executed.returns (HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup finalItems))

theorem build.result (n : Nat) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "build" [.scalar (.int n)] heap (.ref heap.length)
      (heap ++ [encode (List.range' 0 n)]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign (HeapCalls.Evaluates.list .nil)
  apply HeapCalls.BlockReturns.for_range (.cons (HeapCalls.Evaluates.lookup rfl) .nil) rfl
  exact loop_result n 0 n (by omega) _ heap [] rfl

theorem build.«Returns» (n : Int)
    (hn : Calls.Condition program (fun key => if key = "n" then some (.int n) else none)
      HeapRangesAst.requires_build_0) :
    (HeapCalls.call program "build" [.scalar (.int n)] []).Returns := by
  have nonneg : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare hn rfl
  simpa [Int.toNat_of_nonneg nonneg] using (build.result n.toNat []).returns

theorem build.«Supported» (n : Int)
    (hn : Calls.Condition program (fun key => if key = "n" then some (.int n) else none)
      HeapRangesAst.requires_build_0) :
    (HeapCalls.call program "build" [.scalar (.int n)] []).Supported :=
  (build.«Returns» n hn).supported

end tests.py.heap_ranges
