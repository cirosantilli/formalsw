import «.formalsw».tests.py.«comprehensions.py.ast»
import FormalSW

namespace tests.py.comprehensions
open FormalSW.PyAst
private abbrev program := ComprehensionsAst.module
private abbrev values (items : List Int) : List Mutable.Value :=
  items.map (fun value => .scalar (.int value))
private abbrev body (address : Nat) : List Stmt :=
  [.comprehensionAppend address (.name "x")]

private theorem loop.result (heap : Mutable.Heap) (position : Nat) (stop : Int)
    (items : List Int) (env : HeapCalls.Env) :
    ∃ finalEnv finalItems, HeapCalls.BlockContinues program env
      [.rangeStepLoop "x" position stop 1 (body heap.length) []]
      (heap ++ [.list (values items)]) finalEnv (heap ++ [.list (values finalItems)]) := by
  by_cases active : (position : Int) < stop
  · let boundEnv := HeapCalls.setLocal env "x" (.scalar (.int position))
    have emitted : HeapCalls.BlockContinues program boundEnv (body heap.length)
        (heap ++ [.list (values items)]) boundEnv (heap ++ [.list (values (items ++ [(position : Int)]))]) := by
      have write := HeapCalls.BlockContinues.comprehension_append
        (globals := []) (module := program) (env := boundEnv) (address := heap.length)
        (heap := heap ++ [.list (values items)])
        (HeapCalls.Evaluates.lookup (name := "x") rfl)
        (by simp : (heap ++ [.list (values items)])[heap.length]? = some (.list (values items)))
      simpa [body, values, List.map_append] using write
    obtain ⟨finalEnv, finalItems, rest⟩ := loop.result heap (position + 1) stop (items ++ [(position : Int)]) boundEnv
    refine ⟨finalEnv, finalItems, ?_⟩
    apply HeapCalls.BlockContinues.range_step (by simp [Calls.rangeContinues, active])
    simpa [body, Calls.loopContinuation, Calls.loopControl, Int.natCast_add]
      using emitted.append rest
  · exact ⟨env, items, HeapCalls.BlockContinues.range_done
      (by simp [Calls.rangeContinues, active]) HeapCalls.BlockContinues.nil⟩
termination_by stop.toNat - position
decreasing_by omega

private theorem range_copy.result (heap : Mutable.Heap) (n : Int) :
    ∃ items, HeapCalls.ReturnsValue program "range_copy" [.scalar (.int n)] heap
      (.ref heap.length) (heap ++ [.list (values items)]) := by
  let env := HeapCalls.argumentEnv [⟨"n", some (.name "int"), none⟩] [.scalar (.int n)]
  obtain ⟨finalEnv, items, loop⟩ := loop.result heap 0 n []
    (HeapCalls.comprehensionEnv env [("x", .call (.name "range") [.name "n"], [])])
  refine ⟨items, HeapCalls.BlockReturns.function rfl rfl ?_⟩
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.list_comp_range
    (.cons (HeapCalls.Evaluates.lookup (name := "n") rfl) .nil) rfl loop

theorem range_copy.«Returns» (n : Int) :
    (HeapCalls.call program "range_copy" [.scalar (.int n)] []).Returns := by
  obtain ⟨items, executed⟩ := range_copy.result [] n
  exact executed.returns

theorem range_copy.«ReturnType» (n : Int) :
    (HeapCalls.call program "range_copy" [.scalar (.int n)] []).ReturnType "list[int]" := by
  obtain ⟨items, executed⟩ := range_copy.result [] n
  refine .inr ⟨_, [], _, 0, executed.finishes, ?_⟩
  simp only [Mutable.Value.HasType, values, List.nil_append, List.length_nil, List.getElem?_cons_zero]
  refine ⟨_, rfl, Or.inr ⟨"int", rfl, ?_⟩⟩
  simp

theorem range_copy.«Supported» (n : Int) :
    (HeapCalls.call program "range_copy" [.scalar (.int n)] []).Supported :=
  (range_copy.«Returns» n).supported

end tests.py.comprehensions
