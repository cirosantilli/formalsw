import lang.py.FormalSW.CallsRuntimeCostControl

/-! Shared runtime bound for Fibonacci loops. The module parameter remains the
actual source module; adapters prove entry into the loop fragment below. -/
namespace FormalSW.PyAst.Calls.Runtime.Fibonacci
variable (program : Module)
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private def limitName (optimized : Bool) := if optimized then "limit" else "n"
private def termName (optimized : Bool) := if optimized then "a" else "b"
private def term (optimized : Bool) (a b : Nat) := if optimized then a else b
private def iteration (mode : Bool) : List Stmt :=
  [.ifThen (.compare (.binOp (.name (termName mode)) .mod (.constant (.int 2)))
      [(.eq, .constant (.int 0))]) [.augAssign (.name "total") .add (.name (termName mode))] [],
   .assign [.tuple [.name "a", .name "b"]] (.tuple [.name "b", .binOp (.name "a") .add (.name "b")])]

/-- The two loop layouts share the same Fibonacci update and parity test.
Source adapters must reach this exact fragment in their generated AST. -/
def loop (mode : Bool) : List Stmt :=
  if mode then
    [.whileDo (.compare (.name "a") [(.ltE, .name "limit")]) (iteration mode) [],
     .return (.name "total")]
  else
    [.whileDo (.constant (.bool true))
      (.ifThen (.compare (.name "b") [(.gt, .name "n")]) [.return (.name "total")] [] :: iteration mode) []]
private def whileBody (optimized : Bool) : List Stmt :=
  match loop optimized with
  | .whileDo _ body _ :: _ => body
  | _ => []
private def iterationBody (optimized : Bool) : List Stmt :=
  (whileBody optimized).drop (if optimized then 0 else 1)
private def afterGuard (optimized : Bool) := iterationBody optimized ++ loop optimized
private def afterParity (optimized : Bool) := (iterationBody optimized).drop 1 ++ loop optimized

def Locals (optimized : Bool) (n a b total : Nat) (env : ScalarEnv) : Prop :=
  env (limitName optimized) = some (.int n) ∧ env "a" = some (.int a) ∧
  env "b" = some (.int b) ∧ env "total" = some (.int total)

private theorem term_lookup (mode : Bool) (n a b t : Nat) (env : ScalarEnv)
    (valid : Locals mode n a b t env) :
    env (termName mode) = some (.int (term mode a b)) := by
  cases mode with
  | false => exact valid.2.2.1
  | true => exact valid.2.1

private theorem guard_continue (mode : Bool) (n a b t : Nat) (env : ScalarEnv)
    (valid : Locals mode n a b t env) (active : term mode a b ≤ n) :
    RuntimeCost.Reaches (step program) (Runtime.charge .word program) ⟨.block (loop mode) env, []⟩
      (if mode then 9 else 12) ⟨.block (afterGuard mode) env, []⟩ := by
  obtain ⟨hn, ha, hb, ht⟩ := valid
  cases mode with
  | true =>
      have test : Runtime.EvaluatesIn .word program env
          (.compare (.name "a") [(.ltE, .name "limit")]) 7 (.bool true) :=
        Runtime.EvaluatesIn.compare (arithmetic := .word) (ca := 1) (cb := 1) (Runtime.EvaluatesIn.lookup ha) (Runtime.EvaluatesIn.lookup hn)
          (by simp [scalarCompare, evalCmpOp]; exact active)
      exact Runtime.whileTest test (whileBody true) [] [.return (.name "total")] []
  | false =>
      have test : Runtime.EvaluatesIn .word program env
          (.compare (.name "b") [(.gt, .name "n")]) 7 (.bool false) :=
        Runtime.EvaluatesIn.compare (arithmetic := .word) (ca := 1) (cb := 1) (Runtime.EvaluatesIn.lookup hb) (Runtime.EvaluatesIn.lookup hn)
          (by simp [scalarCompare, evalCmpOp]; exact active)
      have lead := Runtime.whileTest (arithmetic := .word) (module := program) (env := env)
        (test := true) Runtime.EvaluatesIn.constant (whileBody false) [] [] []
      have branch := Runtime.branch test [.return (.name "total")] [] (afterGuard false) []
      exact lead.trans branch

private theorem guard_exit (mode : Bool) (n a b t : Nat) (env : ScalarEnv)
    (valid : Locals mode n a b t env) (finished : n < term mode a b) :
    RuntimeCost.Finishes (step program) (Runtime.charge .word program) ⟨.block (loop mode) env, []⟩
      (if mode then 12 else 15) (.ok (.int t)) := by
  obtain ⟨hn, ha, hb, ht⟩ := valid
  have tail (rest : List Stmt) : RuntimeCost.Finishes (step program) (Runtime.charge .word program)
      ⟨.block (.return (.name "total") :: rest) env, []⟩ 3 (.ok (.int t)) :=
    by
      apply RuntimeCost.Finishes.next (amount := 1) (cost := 2)
      · rfl
      · rfl
      · apply RuntimeCost.Finishes.next (amount := 1) (cost := 1) (following := ⟨.value (.int t), []⟩)
        · simp [step, ht, outcome]
        · rfl
        · exact .done rfl rfl
  cases mode with
  | true =>
      have test : Runtime.EvaluatesIn .word program env
          (.compare (.name "a") [(.ltE, .name "limit")]) 7 (.bool false) :=
        Runtime.EvaluatesIn.compare (arithmetic := .word) (ca := 1) (cb := 1) (Runtime.EvaluatesIn.lookup ha) (Runtime.EvaluatesIn.lookup hn)
          (by simp [scalarCompare, evalCmpOp]; exact finished)
      exact (Runtime.whileTest test (whileBody true) [] [.return (.name "total")] []).finishes (tail [])
  | false =>
      have test : Runtime.EvaluatesIn .word program env
          (.compare (.name "b") [(.gt, .name "n")]) 7 (.bool true) :=
        Runtime.EvaluatesIn.compare (arithmetic := .word) (ca := 1) (cb := 1) (Runtime.EvaluatesIn.lookup hb) (Runtime.EvaluatesIn.lookup hn)
          (by simp [scalarCompare, evalCmpOp]; exact finished)
      have lead := Runtime.whileTest (arithmetic := .word) (module := program) (env := env)
        (test := true) Runtime.EvaluatesIn.constant (whileBody false) [] [] []
      have branch := Runtime.branch test [.return (.name "total")] [] (afterGuard false) []
      exact (lead.trans branch).finishes (tail (afterGuard false))

private theorem unpack_cost (mode : Bool) (n a b t : Nat) (env : ScalarEnv)
    (valid : Locals mode n a b t env) :
    ∃ env', Locals mode n b (a + b) t env' ∧
      RuntimeCost.Reaches (step program) (Runtime.charge .word program) ⟨.block (afterParity mode) env, []⟩ 15
        ⟨.block (loop mode) env', []⟩ := by
  obtain ⟨hn, ha, hb, ht⟩ := valid
  let env' := (env.set "a" (.int b)).set "b" (.int (a + b))
  refine ⟨env', ?_, ?_⟩
  · cases mode <;> simpa [Locals, limitName, env', ScalarEnv.set] using And.intro hn ht
  · have right : Runtime.EvaluatesIn .word program env
        (.binOp (.name "a") .add (.name "b")) 6 (.int (a + b)) :=
      Runtime.EvaluatesIn.binary (arithmetic := .word) (work := 1) (ca := 1) (cb := 1) (Runtime.EvaluatesIn.lookup ha) (Runtime.EvaluatesIn.lookup hb)
        (by simp [scalarBinary]) rfl
    have run := Runtime.unpackPair (Runtime.EvaluatesIn.lookup (module := program) hb) right
      "a" "b" (loop mode) []
    cases mode <;> exact run

private theorem iteration_cost (mode : Bool) (n a b t : Nat) (env : ScalarEnv)
    (valid : Locals mode n a b t env) (active : term mode a b ≤ n) :
    ∃ cost t' env', cost ≤ 49 ∧ Locals mode n b (a + b) t' env' ∧
      RuntimeCost.Reaches (step program) (Runtime.charge .word program) ⟨.block (loop mode) env, []⟩ cost
        ⟨.block (loop mode) env', []⟩ := by
  have guard := guard_continue program mode n a b t env valid active
  have getTerm := term_lookup mode n a b t env valid
  have parity : Runtime.EvaluatesIn .word program env
      (.compare (.binOp (.name (termName mode)) .mod (.constant (.int 2)))
        [(.eq, .constant (.int 0))]) 12 (.bool (decide (term mode a b % 2 = 0))) := by
    apply Runtime.EvaluatesIn.compare (ca := 6) (cb := 1) (av := .int ↑(term mode a b % 2)) (bv := .int 0)
    · exact Runtime.EvaluatesIn.binary (arithmetic := .word) (work := 1) (ca := 1) (cb := 1) (Runtime.EvaluatesIn.lookup getTerm) Runtime.EvaluatesIn.constant
        (by simp [scalarBinary]) rfl
    · exact Runtime.EvaluatesIn.constant
    · simp [scalarCompare, evalCmpOp]
      omega
  have branch := Runtime.branch parity [.augAssign (.name "total") .add (.name (termName mode))]
    [] (afterParity mode) []
  by_cases even : term mode a b % 2 = 0
  · have add : Runtime.EvaluatesIn .word program env
        (.binOp (.name "total") .add (.name (termName mode))) 6 (.int (t + term mode a b)) :=
      Runtime.EvaluatesIn.binary (arithmetic := .word) (work := 1) (ca := 1) (cb := 1) (Runtime.EvaluatesIn.lookup valid.2.2.2) (Runtime.EvaluatesIn.lookup getTerm)
        (by simp [scalarBinary]) rfl
    have assigned := Runtime.augAssign add (afterParity mode) []
    have valid' : Locals mode n a b (t + term mode a b) (env.set "total" (.int (t + term mode a b))) := by
      obtain ⟨hn, ha, hb, ht⟩ := valid
      cases mode <;> simpa [Locals, ScalarEnv.set, limitName] using And.intro hn (And.intro ha hb)
    obtain ⟨env', valid', unpack⟩ := unpack_cost program mode n a b (t + term mode a b) _ valid'
    have bodyRun : RuntimeCost.Reaches (step program) (Runtime.charge .word program) ⟨.block (afterGuard mode) env, []⟩ 37
        ⟨.block (loop mode) env', []⟩ := by
      have branch' := branch
      simp only [even, decide_true, ↓reduceIte] at branch'
      cases mode <;> exact (branch'.trans assigned).trans unpack
    exact ⟨_, _, env', by cases mode <;> decide, valid', guard.trans bodyRun⟩
  · obtain ⟨env', valid', unpack⟩ := unpack_cost program mode n a b t env valid
    have bodyRun : RuntimeCost.Reaches (step program) (Runtime.charge .word program) ⟨.block (afterGuard mode) env, []⟩ 29
        ⟨.block (loop mode) env', []⟩ := by
      have branch' := branch
      simp only [even, decide_false, Bool.false_eq_true, ↓reduceIte, List.nil_append] at branch'
      cases mode <;> exact branch'.trans unpack
    exact ⟨_, _, env', by cases mode <;> decide, valid', guard.trans bodyRun⟩

/-- Two source iterations change `(a,b)` to `(a+b,a+2*b)`. Since `a<b`,
the first component at least doubles, consuming one power-of-two budget. -/
theorem loop_bound (mode : Bool) (n k a b t : Nat) (env : ScalarEnv)
    (positive : 0 < a) (ordered : a < b) (budget : n < 2 ^ k * a)
    (valid : Locals mode n a b t env) :
    ∃ cost value, RuntimeCost.Finishes (step program) (Runtime.charge .word program) ⟨.block (loop mode) env, []⟩ cost (.ok value) ∧
      cost ≤ 98 * k + 15 := by
  have exitBound : (if mode then 12 else 15) ≤ 15 := by cases mode <;> decide
  induction k generalizing a b t env with
  | zero =>
      have finished : n < term mode a b := by
        simp only [Nat.pow_zero, Nat.one_mul] at budget
        cases mode <;> simp only [term, Bool.false_eq_true, ↓reduceIte] <;> omega
      exact ⟨_, .int t, guard_exit program mode n a b t env valid finished, by cases mode <;> decide⟩
  | succ k ih =>
      by_cases active : term mode a b ≤ n
      · obtain ⟨firstCost, t', env', firstBound, valid', first⟩ :=
          iteration_cost program mode n a b t env valid active
        by_cases active' : term mode b (a + b) ≤ n
        · obtain ⟨secondCost, t'', env'', secondBound, valid'', second⟩ :=
            iteration_cost program mode n b (a + b) t' env' valid' active'
          have nextBudget : n < 2 ^ k * (a + b) := by
            rw [Nat.pow_succ, Nat.mul_assoc] at budget
            exact Nat.lt_of_lt_of_le budget (Nat.mul_le_mul_left _ (by omega : 2 * a ≤ a + b))
          obtain ⟨cost, value, tail, bounded⟩ := ih (a + b) (b + (a + b)) t'' env''
            (by omega) (by omega) nextBudget valid''
          exact ⟨_, value, (first.trans second).finishes tail, by omega⟩
        · have tail := guard_exit program mode n b (a + b) t' env' valid' (by omega)
          exact ⟨_, .int t', first.finishes tail, by omega⟩
      · have tail := guard_exit program mode n a b t env valid (by omega)
        exact ⟨_, .int t, tail, by omega⟩


/-- A logarithmic bound from positive, ordered initial Fibonacci values. -/
theorem bound (mode : Bool) (n : Nat) (env : ScalarEnv) (valid : Locals mode n 1 2 0 env) :
    ∃ cost value, RuntimeCost.Finishes (step program) (Runtime.charge .word program)
      ⟨.block (loop mode) env, []⟩ cost (.ok value) ∧
      cost ≤ 98 * (Nat.log2 n + 1) + 15 := by
  have budget : n < 2 ^ (Nat.log2 n + 1) * 1 := by
    rw [Nat.mul_one]
    by_cases zero : n = 0
    · subst n; decide
    · exact (Nat.log2_lt zero).mp (by omega)
  exact loop_bound program mode n (Nat.log2 n + 1) 1 2 0 env
    (by decide) (by decide) budget valid

end FormalSW.PyAst.Calls.Runtime.Fibonacci
