import lang.py.FormalSW.HeapRuntimeCostRangeSums
import lang.py.FormalSW.HeapRuntimeCostListCopies

open FormalSW.PyAst HeapCalls HeapCalls.Runtime
private def program : Module := { body := [] }
private def env : HeapCalls.Env := fun _ => none

/-- Range setup examines only its arguments; integer widths follow the chosen model. -/
example : operation .word [] (.sumGenerator (.name "i") [("i", .call (.name "range") [], [])] env (.constant (.int 0)))
    [.scalar (.int 0), .scalar (.int (2^100))] = some 4 := rfl
example : operation .bits [] (.sumGenerator (.name "i") [("i", .call (.name "range") [], [])] env (.constant (.int 0)))
    [.scalar (.int 0), .scalar (.int (2^100))] = some 104 := by decide
example : operation .word [] (.sumGenerator (.name "i") [("i", .call (.name "range") [], [])] env (.constant (.int 0)))
    [.ref 0] = none := rfl

/-- Signed endpoints include empty negative ranges. The proof runs every summand. -/
example (n : Int) (heap : Heap) : ∃ extra, ∃ answer : Int,
    EvaluatesIn .word program env (.sumRange "i" (.name "i") [.constant (.int n)] []) heap
      (12*n.toNat+18) (.scalar (.int answer)) (heap ++ extra) := by
  let summed := setLocal (comprehensionEnv env [("i", .call (.name "range") [.constant (.int n)], [])])
    sumAccumulator (.scalar (.int 0))
  obtain ⟨extra, answer, loop⟩ := range_sum_loop (globals := []) (module := program) (.name "i") "i" 1 (fun _ => True) (by decide)
    (by intros; trivial)
    (by intro heap env i _ lookup; exact ⟨[], i, by simpa using EvaluatesIn.lookup lookup⟩)
    n.toNat 0 n 0 (by simp) heap summed trivial rfl
  have run := EvaluatesIn.sum_range (EvaluatesIn.sum_generator_range (work := 3)
    (ArgumentsIn.cons (EvaluatesIn.constant (module := program) (env := env) (value := .int n)) ArgumentsIn.nil)
    rfl EvaluatesIn.constant rfl loop)
  exact ⟨extra, answer, run.mono (by simp only [PrimitiveWork.integer]; omega)⟩

/-- A summand may allocate: list construction, indexing and retained credits are all paid. -/
example (n : Int) (heap : Heap) : ∃ extra, ∃ answer : Int,
    EvaluatesIn .word program env
      (.sumRange "i" (.subscript (.list [.name "i"]) (.constant (.int 0))) [.constant (.int n)] []) heap
      (27*n.toNat+18) (.scalar (.int answer)) (heap ++ extra) := by
  let element := Expr.subscript (.list [.name "i"]) (.constant (.int 0))
  let summed := setLocal (comprehensionEnv env [("i", .call (.name "range") [.constant (.int n)], [])])
    sumAccumulator (.scalar (.int 0))
  have evaluated : ∀ heap env (i : Int), True → env "i" = some (.scalar (.int i)) →
      ∃ extra, ∃ value : Int, EvaluatesIn .word program env element heap 16
        (.scalar (.int value)) (heap ++ extra) := by
    intro heap env i _ lookup
    refine ⟨[.list [.scalar (.int i)]], i, ?_⟩
    apply EvaluatesIn.list_subscript (items := [.scalar (.int i)]) (offset := 0) (ca := 7) (cb := 1)
      (by intros; simp) (EvaluatesIn.list (ArgumentsIn.cons (EvaluatesIn.lookup lookup) ArgumentsIn.nil))
      EvaluatesIn.constant (by simp)
    simpa using Mutable.getItem_list (heap ++ [.list [.scalar (.int i)]]) heap.length 0
      [.scalar (.int i)] (by simp) (by simp)
  obtain ⟨extra, answer, loop⟩ := range_sum_loop element "i" 16 (fun _ => True) (by decide)
    (by intros; trivial) evaluated n.toNat 0 n 0 (by simp) heap summed trivial rfl
  have run := EvaluatesIn.sum_range (EvaluatesIn.sum_generator_range (work := 3)
    (ArgumentsIn.cons (EvaluatesIn.constant (module := program) (env := env) (value := .int n)) ArgumentsIn.nil)
    rfl EvaluatesIn.constant rfl loop)
  exact ⟨extra, answer, run.mono (by simp only [PrimitiveWork.integer]; omega)⟩
