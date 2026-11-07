import lang.py.FormalSW.HeapRuntimeCostComprehensions
import lang.py.FormalSW.HeapRuntimeInputs

/-! Range comprehensions retain one output array. These rules charge element
execution, every range guard, and amortized writes including resizing copies. -/
namespace FormalSW.PyAst.HeapCalls.Runtime
open NestedIntList (encode)

/-- Collect scalar integer results over a unit-stride interval. The element
may read the retained heap; the result array and captured bindings are preserved. -/
theorem collect_range_loop (module : Module) (heap : Heap) (element : Expr) (name : String)
    (first stop : Int) (elementCost : Nat) (invariant : HeapCalls.Env → Prop)
    (preserve : ∀ env i, invariant env → invariant (setLocal env name (.scalar (.int i))))
    (evaluate : ∀ (items : List Int) env (i : Int), first ≤ i → i < stop →
      invariant env → env name = some (.scalar (.int i)) →
      ∃ value : Int, EvaluatesIn .word module env element (heap ++ [.list (encode items)])
        elementCost (.scalar (.int value)) (heap ++ [.list (encode items)]))
    (remaining : Nat) (next : Int) (endpoint : remaining = (stop-next).toNat)
    (lower : first ≤ next) (items : List Int) (env : HeapCalls.Env) (saved : invariant env) :
    ∃ finalItems finalEnv,
      BlockContinuesIn .word module env
        [.rangeStepLoop name next stop 1 [.comprehensionAppend heap.length element] []]
        (heap ++ [.list (encode items)]) ((elementCost+11)*remaining+4) finalEnv
        (heap ++ [.list (encode finalItems)]) ∧
      finalItems.length = items.length+remaining ∧ invariant finalEnv := by
  induction remaining generalizing next items env with
  | zero =>
      refine ⟨items, env, ?_, by simp, saved⟩
      exact BlockContinuesIn.range_done (by simp [Calls.rangeContinues]; omega) BlockContinuesIn.nil
  | succ remaining ih =>
      let indexed := setLocal env name (.scalar (.int next))
      have indexedSaved : invariant indexed := preserve env next saved
      obtain ⟨value, evaluated⟩ := evaluate items indexed next lower (by omega) indexedSaved (by simp [indexed, setLocal])
      have appended : BlockContinuesIn .word module indexed [.comprehensionAppend heap.length element]
          (heap ++ [.list (encode items)]) (elementCost+7) indexed
          (heap ++ [.list (encode (items ++ [value]))]) := by
        have run := BlockContinuesIn.comprehension_append (address := heap.length) evaluated
          (by simp : (heap ++ [.list (encode items)])[heap.length]? = some (.list (encode items)))
        simpa [encode, List.set_append] using run
      obtain ⟨finalItems, finalEnv, rest, length, finalSaved⟩ := ih (next+1) (by omega) (by omega)
        (items ++ [value]) indexed indexedSaved
      refine ⟨finalItems, finalEnv, ?_, ?_, finalSaved⟩
      · have run := BlockContinuesIn.range_step (env := env) (name := name)
          (by simp [Calls.rangeContinues]; omega : Calls.rangeContinues next stop 1 = true)
          (by simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt] using appended.append rest)
        exact run.mono (by simp only [Nat.mul_add, Nat.mul_one]; omega)
      · simp only [List.length_append, List.length_singleton] at length
        omega

/-- Two range generators append into the same array, including when one or both
ranges are empty. The inner endpoint is reevaluated for every outer iteration. -/
theorem collect_rectangle_loop (module : Module) (heap : Heap) (element innerBound : Expr)
    (rowName columnName : String) (different : rowName ≠ columnName)
    (rows columns : Int) (elementCost boundCost : Nat) (invariant : HeapCalls.Env → Prop)
    (preserveRow : ∀ env i, invariant env → invariant (setLocal env rowName (.scalar (.int i))))
    (preserveColumn : ∀ env i, invariant env → invariant (setLocal env columnName (.scalar (.int i))))
    (bound : ∀ (items : List Int) env, invariant env →
      EvaluatesIn .word module env innerBound (heap ++ [.list (encode items)]) boundCost
        (.scalar (.int columns)) (heap ++ [.list (encode items)]))
    (evaluate : ∀ (items : List Int) env (r c : Int), 0 ≤ r → r < rows → 0 ≤ c → c < columns →
      invariant env → env rowName = some (.scalar (.int r)) → env columnName = some (.scalar (.int c)) →
      ∃ value : Int, EvaluatesIn .word module env element (heap ++ [.list (encode items)])
        elementCost (.scalar (.int value)) (heap ++ [.list (encode items)]))
    (remaining : Nat) (next : Int) (endpoint : remaining = (rows-next).toNat)
    (lower : 0 ≤ next) (items : List Int) (env : HeapCalls.Env) (saved : invariant env) :
    ∃ finalItems finalEnv,
      BlockContinuesIn .word module env
        [.rangeStepLoop rowName next rows 1
          [.forIn (.name columnName) (.call (.name "range") [innerBound]) [.comprehensionAppend heap.length element] []] []]
        (heap ++ [.list (encode items)])
        (((elementCost+11)*columns.toNat+boundCost+12)*remaining+4) finalEnv
        (heap ++ [.list (encode finalItems)]) ∧
      finalItems.length = items.length+remaining*columns.toNat ∧ invariant finalEnv := by
  induction remaining generalizing next items env with
  | zero =>
      refine ⟨items, env, ?_, by simp, saved⟩
      exact BlockContinuesIn.range_done (by simp [Calls.rangeContinues]; omega) BlockContinuesIn.nil
  | succ remaining ih =>
      let indexed := setLocal env rowName (.scalar (.int next))
      let innerInvariant := fun env => invariant env ∧ env rowName = some (.scalar (.int next))
      have indexedSaved : innerInvariant indexed := ⟨preserveRow env next saved, by simp [indexed, setLocal]⟩
      have preserve : ∀ env i, innerInvariant env → innerInvariant (setLocal env columnName (.scalar (.int i))) := by
        intro env i h
        exact ⟨preserveColumn env i h.1, by simpa [setLocal, different] using h.2⟩
      obtain ⟨middleItems, middleEnv, inner, length, middleSaved⟩ := collect_range_loop module heap element
        columnName 0 columns elementCost innerInvariant preserve
        (by
          intro items env c lowerColumn upperColumn h getColumn
          exact evaluate items env next c lower (by omega) lowerColumn upperColumn h.1 h.2 getColumn)
        columns.toNat 0 (by simp) (by omega) items indexed indexedSaved
      have body := BlockContinuesIn.for_range_bound (bound items indexed indexedSaved.1) inner
      obtain ⟨finalItems, finalEnv, rest, finalLength, finalSaved⟩ := ih (next+1) (by omega) (by omega)
        middleItems middleEnv middleSaved.1
      refine ⟨finalItems, finalEnv, ?_, ?_, finalSaved⟩
      · have run := BlockContinuesIn.range_step (env := env) (name := rowName)
          (by simp [Calls.rangeContinues]; omega : Calls.rangeContinues next rows 1 = true)
          (by simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt] using body.append rest)
        exact run.mono (by simp only [Nat.mul_add, Nat.mul_one]; omega)
      · simp only [Nat.succ_mul]
        omega

end FormalSW.PyAst.HeapCalls.Runtime
