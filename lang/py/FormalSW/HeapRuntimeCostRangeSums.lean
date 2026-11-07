import lang.py.FormalSW.HeapRuntimeCostSumGenerators
import lang.py.FormalSW.HeapRuntimeCostReturns

namespace FormalSW.PyAst.HeapCalls.Runtime
variable {globals : Mutable.Globals}

/-- Range arguments and the initial sum are evaluated once, before lazy iteration. -/
theorem EvaluatesIn.sum_generator_range
    (arguments : ArgumentsIn (globals := globals) arithmetic module env 0 expressions heap ca values middle)
    (bounds : rangeBounds values = .ok (first, stop, stride))
    (started : EvaluatesIn (globals := globals) arithmetic module env start middle cb (.scalar (.int initial)) afterStart)
    (priced : operation arithmetic middle
      (.sumGenerator element [(name, .call (.name "range") expressions, filters)] env start) values = some work)
    (loop : BlockReturnsIn (globals := globals) arithmetic module
      (setLocal (comprehensionEnv env [(name, .call (.name "range") expressions, filters)])
        sumAccumulator (.scalar (.int initial)))
      [.rangeStepLoop name first stop stride (comprehensionFilters filters (sumBody element [])) [],
        .return (.name sumAccumulator)] afterStart budget answer finalHeap) :
    EvaluatesIn (globals := globals) arithmetic module env
      (.sumGenerator element [(name, .call (.name "range") expressions, filters)] start)
      heap (ca+cb+budget+work+PrimitiveWork.integer arithmetic initial+4) answer finalHeap := by
  intro anchors stack
  let generators := [(name, Expr.call (.name "range") expressions, filters)]
  let op := Operation.sumGenerator element generators env start
  let localEnv := comprehensionEnv env generators
  let body := comprehensionFilters filters (sumBody element [])
  have firstStep : Reaches (globals := globals) arithmetic module anchors
      ⟨.expr (.sumGenerator element generators start) env, stack, heap⟩ 1
      (argumentsState op env [] expressions stack heap) := advance rfl rfl (by cases expressions <;> rfl)
  have ready : Reaches (globals := globals) arithmetic module anchors ⟨.operation op values, stack, middle⟩ (work+1)
      ⟨.expr start env, .sumStart (.rangeStepLoop name first stop stride body []) localEnv :: stack, middle⟩ :=
    advance (by simp [step, op, generators, sumGeneratorStart, bounds, body, localEnv])
      (by simp [charge, op, generators, priced]) rfl
  have enter : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar (.int initial)), .sumStart (.rangeStepLoop name first stop stride body []) localEnv :: stack, afterStart⟩
      (PrimitiveWork.integer arithmetic initial+1)
      ⟨.block [.rangeStepLoop name first stop stride body [], .return (.name sumAccumulator)]
        (setLocal localEnv sumAccumulator (.scalar (.int initial))), .generatorEnd :: stack, afterStart⟩ :=
    advance rfl rfl rfl
  have finish : Reaches (globals := globals) arithmetic module anchors
      ⟨.value answer, .generatorEnd :: stack, finalHeap⟩ 1 ⟨.value answer, stack, finalHeap⟩ := advance rfl rfl rfl
  exact ((((((firstStep.trans (arguments.reaches op anchors stack)).trans ready).trans
    (started anchors _)).trans enter).trans (loop anchors (.generatorEnd :: stack))).trans finish).mono (by omega)

/-- The legacy range-sum expression performs one lowering step. -/
theorem EvaluatesIn.sum_range
    (run : EvaluatesIn (globals := globals) arithmetic module env
      (.sumGenerator element [(name, .call (.name "range") bounds, filters)] (.constant (.int 0)))
      heap budget answer finalHeap) :
    EvaluatesIn (globals := globals) arithmetic module env (.sumRange name element bounds filters) heap (budget+1) answer finalHeap := by
  intro anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.expr (.sumRange name element bounds filters) env, stack, heap⟩ 1
      ⟨.expr (.sumGenerator element [(name, .call (.name "range") bounds, filters)] (.constant (.int 0))) env, stack, heap⟩ :=
    advance rfl rfl rfl
  exact (first.trans (run anchors stack)).mono (by omega)

/-- Uniform element work composes through a unit-stride sum, preserving appended heap effects. -/
theorem range_sum_loop_invariant (element : Expr) (name : String) (elementCost : Nat)
    (invariant : Env → Prop) (privateName : name ≠ sumAccumulator)
    (preserved : ∀ env key value, invariant env →
      (key = name ∨ key = sumAccumulator) → invariant (setLocal env key value))
    (heapInvariant : Heap → Prop)
    (heapPreserved : ∀ heap extra, heapInvariant heap → heapInvariant (heap ++ extra))
    (lower stop : Int)
    (evaluated : ∀ heap env (i : Int), heapInvariant heap → lower ≤ i → i < stop →
      invariant env → env name = some (.scalar (.int i)) →
      ∃ extra, ∃ value : Int, EvaluatesIn (globals := globals) .word module env element heap elementCost
        (.scalar (.int value)) (heap ++ extra))
    (remaining : Nat) (first initial : Int) (endpoint : remaining = (stop-first).toNat)
    (heap : Heap) (env : Env) (heapSaved : heapInvariant heap) (above : lower ≤ first)
    (saved : invariant env)
    (accumulator : env sumAccumulator = some (.scalar (.int initial))) :
    ∃ extra, ∃ answer : Int, BlockReturnsIn (globals := globals) .word module env
      [.rangeStepLoop name first stop 1 (sumBody element []) [], .return (.name sumAccumulator)] heap
      ((elementCost+11)*remaining+6) (.scalar (.int answer)) (heap ++ extra) := by
  induction remaining generalizing first initial heap env with
  | zero =>
      refine ⟨[], initial, ?_⟩
      have ended := BlockContinuesIn.range_done (globals := globals) (module := module) (name := name)
        (next := first) (stop := stop) (stride := 1) (body := sumBody element [])
        (by simp [Calls.rangeContinues]; omega) (BlockContinuesIn.nil (env := env) (heap := heap))
      simpa using ended.returns (BlockReturnsIn.return_value (EvaluatesIn.lookup accumulator))
  | succ remaining ih =>
      let withIndex := setLocal env name (.scalar (.int first))
      have indexSaved : invariant withIndex := preserved env name _ saved (Or.inl rfl)
      have indexAccumulator : withIndex sumAccumulator = some (.scalar (.int initial)) := by
        simpa [withIndex, setLocal, Ne.symm privateName] using accumulator
      obtain ⟨extra, value, item⟩ := evaluated heap withIndex first heapSaved above (by omega) indexSaved (by simp [withIndex, setLocal])
      have added := EvaluatesIn.binary (op := .add) (work := 1) (av := .int initial) (bv := .int value)
        (EvaluatesIn.lookup indexAccumulator) item rfl rfl
      let withSum := setLocal withIndex sumAccumulator (.scalar (.int (initial+value)))
      have sumSaved : invariant withSum := preserved withIndex sumAccumulator _ indexSaved (Or.inr rfl)
      obtain ⟨later, answer, tail⟩ := ih (first+1) (initial+value) (by omega) (heap ++ extra) withSum (heapPreserved heap extra heapSaved) (by omega) sumSaved
        (by simp [withSum, setLocal])
      refine ⟨extra ++ later, answer, ?_⟩
      have active : Calls.rangeContinues first stop 1 = true := by simp [Calls.rangeContinues]; omega
      have run := BlockReturnsIn.range_step (module := module) (env := env) (name := name)
        (body := sumBody element []) (otherwise := []) (following := [.return (.name sumAccumulator)]) active
        (by simpa only [sumBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, Bool.false_eq_true, reduceIte, List.append_assoc] using BlockReturnsIn.assign added tail)
      exact run.mono (by simp only [Nat.mul_add, Nat.mul_one]; omega)

/-- Uniform element work without restrictions on the initial heap or range. -/
theorem range_sum_loop (element : Expr) (name : String) (elementCost : Nat)
    (invariant : Env → Prop) (privateName : name ≠ sumAccumulator)
    (preserved : ∀ env key value, invariant env →
      (key = name ∨ key = sumAccumulator) → invariant (setLocal env key value))
    (evaluated : ∀ heap env (i : Int), invariant env → env name = some (.scalar (.int i)) →
      ∃ extra, ∃ value : Int, EvaluatesIn (globals := globals) .word module env element heap elementCost
        (.scalar (.int value)) (heap ++ extra))
    (remaining : Nat) (first stop initial : Int) (endpoint : remaining = (stop-first).toNat)
    (heap : Heap) (env : Env) (saved : invariant env)
    (accumulator : env sumAccumulator = some (.scalar (.int initial))) :
    ∃ extra, ∃ answer : Int, BlockReturnsIn (globals := globals) .word module env
      [.rangeStepLoop name first stop 1 (sumBody element []) [], .return (.name sumAccumulator)] heap
      ((elementCost+11)*remaining+6) (.scalar (.int answer)) (heap ++ extra) :=
  range_sum_loop_invariant element name elementCost invariant privateName preserved
    (fun _ => True) (by intros; trivial) first stop
    (fun heap env i _ _ _ => evaluated heap env i)
    remaining first initial endpoint heap env trivial (by omega) saved accumulator

end FormalSW.PyAst.HeapCalls.Runtime
