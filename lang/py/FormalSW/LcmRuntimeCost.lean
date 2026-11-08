import lang.py.FormalSW.CallsRuntimeCostRanges
import lang.py.FormalSW.PrimitiveWorkBounds

/-! Runtime bounds for a range fold using gcd to accumulate least common multiples.
The source adapters check the actual AST, including the order of multiplication
and division. Fixed-cost arithmetic still charges gcd by its operand widths. -/
namespace FormalSW.PyAst.Calls.Runtime.Lcm

structure GcdBinding (program : Module) : Prop where
  imported : importedFunction program.body "gcd" = some ("math", "gcd")
  absent : findFunctionIn program.body "gcd" = none

def accName (optimized : Bool) := if optimized then "ans" else "acc"
def update (optimized : Bool) : Expr :=
  let acc := .name (accName optimized)
  let x := .name "x"
  let divisor := .call (.name "gcd") [acc, x]
  if optimized then .binOp (.binOp acc .floorDiv divisor) .mult x
  else .binOp (.binOp acc .mult x) .floorDiv divisor

def body (optimized : Bool) : List Stmt := [.assign [.name (accName optimized)] (update optimized)]
def loop (optimized : Bool) (start stop : Int) : List Stmt :=
  [.rangeStepLoop "x" start stop 1 (body optimized) [], .return (.name (accName optimized))]

private def width (acc x : Nat) := min (PrimitiveWork.bitLength (acc : Int)) (PrimitiveWork.bitLength (x : Int))

private theorem gcd_cost (program : Module) (binding : GcdBinding program)
    (optimized : Bool) (acc x : Nat) (env : ScalarEnv)
    (ha : env (accName optimized) = some (.int acc)) (hx : env "x" = some (.int x)) :
    EvaluatesIn .word program env (.call (.name "gcd") [.name (accName optimized), .name "x"])
      (width acc x + 8) (.int (Nat.gcd acc x)) := by
  have semantic : libraryCall program "gcd" [.int acc, .int x] = some (.ok (.int (Nat.gcd acc x))) := by
    simp only [libraryCall, libraryFunction, binding.imported, Option.map_some]
    simpa using congrArg some (Math.gcdCall_pair (acc : Int) (x : Int))
  have measured : library .word program "gcd" [.int acc, .int x] = some (width acc x + 1) := by
    simp [library, binding.imported, scalarNumber, width]
  have run := EvaluatesIn.library_pair (arithmetic := .word) (work := width acc x + 1)
    (EvaluatesIn.lookup ha) (EvaluatesIn.lookup hx) binding.absent semantic measured
  have costEq : 1 + 1 + (width acc x + 1) + 5 = width acc x + 8 := by omega
  rw [costEq] at run
  exact run

private theorem update_cost (program : Module) (binding : GcdBinding program)
    (optimized : Bool) (acc x : Nat) (positive : 0 < x)
    (env : ScalarEnv) (ha : env (accName optimized) = some (.int acc))
    (hx : env "x" = some (.int x)) :
    ∃ answer : Nat, EvaluatesIn .word program env (update optimized)
      (width acc x + 18) (.int answer) := by
  have divisor := gcd_cost program binding optimized acc x env ha hx
  cases optimized with
  | false =>
      refine ⟨acc * x / Nat.gcd acc x, ?_⟩
      have product : EvaluatesIn .word program env (.binOp (.name "acc") .mult (.name "x"))
          6 (.int (acc * x)) :=
        EvaluatesIn.binary (arithmetic := .word) (work := 1) (ca := 1) (cb := 1)
          (EvaluatesIn.lookup ha) (EvaluatesIn.lookup hx) (by simp [scalarBinary]) rfl
      have result : scalarBinary .floorDiv (.int (acc * x)) (.int (Nat.gcd acc x)) =
          some (.ok (.int (acc * x / Nat.gcd acc x : Nat))) := by
        simp [scalarBinary, positive, Nat.ne_of_gt positive]
      have run := EvaluatesIn.binary (work := 1) product divisor result rfl
      have costEq : 6 + (width acc x + 8) + 1 + 3 = width acc x + 18 := by omega
      rw [costEq] at run
      exact run
  | true =>
      refine ⟨acc / Nat.gcd acc x * x, ?_⟩
      have result : scalarBinary .floorDiv (.int acc) (.int (Nat.gcd acc x)) =
          some (.ok (.int (acc / Nat.gcd acc x : Nat))) := by
        simp [scalarBinary, positive, Nat.ne_of_gt positive]
      have quotient := EvaluatesIn.binary (work := 1) (EvaluatesIn.lookup ha) divisor result rfl
      have run := EvaluatesIn.binary (op := .mult) (work := 1) quotient (EvaluatesIn.lookup hx)
        (value := .int (acc / Nat.gcd acc x * x : Nat)) (by simp [scalarBinary]) rfl
      have costEq : (1 + (width acc x + 8) + 1 + 3) + 1 + 1 + 3 = width acc x + 18 := by omega
      rw [costEq] at run
      exact run

/-- Each iteration costs at most log₂ N plus a fixed amount, even when the
accumulator is much larger than N: gcd depends on the smaller operand width. -/
theorem loop_bound (program : Module) (binding : GcdBinding program)
    (optimized : Bool) (N remaining : Nat) (start : Int) (env : ScalarEnv) (acc : Nat)
    (positive : 0 < start) (endpoint : (N : Int) + 1 = start + remaining)
    (ha : env (accName optimized) = some (.int acc)) :
    ∃ cost answer, RuntimeCost.Finishes (step program) (charge .word program)
      ⟨.block (loop optimized start (N + 1)) env, []⟩ cost (.ok (.int answer)) ∧
      cost ≤ (Nat.log2 N + 25) * remaining + 7 := by
  let invariant := fun (i : Int) (env : ScalarEnv) =>
    0 < i ∧ ∃ acc : Nat, env (accName optimized) = some (.int acc)
  have iteration : ∀ i env, i < (N : Int) + 1 → invariant i env → ∀ stack,
      ∃ cost env', invariant (i + 1) env' ∧ RuntimeCost.Reaches (step program) (charge .word program)
        ⟨.block (body optimized ++ [loopContinuation (body optimized)
          (.rangeStepLoop "x" (i + 1) (N + 1) 1 (body optimized) [])] ++ [.return (.name (accName optimized))])
          (env.set "x" (.int i)), stack⟩ cost
        ⟨.block (loop optimized (i + 1) (N + 1)) env', stack⟩ ∧ cost ≤ Nat.log2 N + 21 := by
    intro i env within valid stack
    obtain ⟨pos, acc, getAcc⟩ := valid
    have cast : (i.toNat : Int) = i := Int.toNat_of_nonneg (by omega)
    have bound : i.toNat ≤ N := by omega
    have getAcc' : (env.set "x" (.int i)) (accName optimized) = some (.int acc) := by
      cases optimized <;> simpa [ScalarEnv.set, accName] using getAcc
    obtain ⟨answer, evaluated⟩ := update_cost program binding optimized acc i.toNat (by omega)
      (env.set "x" (.int i)) getAcc' (by simp [ScalarEnv.set, cast])
    let env' := (env.set "x" (.int i)).set (accName optimized) (.int answer)
    have run := assign evaluated (accName optimized) (loop optimized (i + 1) (N + 1)) stack
    refine ⟨width acc i.toNat + 18 + 2, env', ⟨by omega, answer, by simp [env', ScalarEnv.set]⟩, ?_, ?_⟩
    · cases optimized <;> exact run
    · have smaller := Nat.min_le_right (PrimitiveWork.bitLength (acc : Int)) (PrimitiveWork.bitLength (i.toNat : Int))
      have logarithm := PrimitiveWork.log2_mono bound
      simp only [PrimitiveWork.bitLength, Int.natAbs_natCast] at smaller
      simp only [width, PrimitiveWork.bitLength, Int.natAbs_natCast]
      omega
  obtain ⟨cost, final, valid, run, bound⟩ := rangeLoopWithin .word program "x" (body optimized)
    [.return (.name (accName optimized))] (N + 1) invariant 4 (Nat.log2 N + 21)
    (fun _ _ _ => Nat.le_refl 4) iteration remaining start env endpoint ⟨positive, acc, ha⟩ []
  obtain ⟨_, answer, getAnswer⟩ := valid
  have tail : RuntimeCost.Finishes (step program) (charge .word program)
      ⟨.block [.return (.name (accName optimized))] final, []⟩ 3 (.ok (.int answer)) := by
    apply RuntimeCost.Finishes.next (amount := 1) (cost := 2)
    · rfl
    · rfl
    · apply RuntimeCost.Finishes.next (amount := 1) (cost := 1) (following := ⟨.value (.int answer), []⟩)
      · simp [step, getAnswer, outcome]
      · rfl
      · exact .done rfl rfl
  have coefficient : Nat.log2 N + 21 + 4 = Nat.log2 N + 25 := by omega
  rw [coefficient] at bound
  exact ⟨cost + 3, answer, run.finishes tail, by omega⟩

/-- Absorb setup and per-iteration constants into the asymptotic bound. -/
theorem budget_bound (n : Nat) (large : 2 ≤ n) :
    (Nat.log2 n + 25) * n + 26 ≤ 64 * (n * Nat.log2 n) := by
  have positive : 1 ≤ Nat.log2 n := (Nat.le_log2 (by omega)).mpr (by simpa using large)
  have product : n ≤ n * Nat.log2 n := by
    simpa using Nat.mul_le_mul_left n positive
  rw [Nat.add_mul, Nat.mul_comm (Nat.log2 n) n]
  omega

end FormalSW.PyAst.Calls.Runtime.Lcm
