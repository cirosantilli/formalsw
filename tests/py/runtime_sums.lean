import lang.py.FormalSW.HeapRuntimeCostSums
import lang.py.FormalSW.DecimalSumRuntimeCost

open FormalSW.PyAst HeapCalls HeapCalls.Runtime
private def program : Module := { body := [] }

/-- Iterator acquisition is separate from the linear traversal below. -/
example : charge .word program
    ⟨.operation .sumSequence [.ref 0, .scalar (.int 7)], [],
      [.list [.scalar (.int (-3)), .scalar (.int 5)]]⟩ = some 3 := rfl
example : charge .word program
    ⟨.block [.sequenceStepLoop sumItem (.ref 0) 0 (sumBody (.name sumItem) []) []]
      (fun _ => none), [], [.list [.scalar (.int (-3)), .scalar (.int 5)]]⟩ = some 5 := rfl

/-- Signed values and a nonzero starting accumulator are included in the sum. -/
example : EvaluatesIn .word program (fun _ => some (.ref 0))
    (.sumSequence (.name "xs") (.constant (.int 7)))
    [.list [.scalar (.int (-3)), .scalar (.int 5)]] 42 (.scalar (.int 9))
    [.list [.scalar (.int (-3)), .scalar (.int 5)]] :=
  EvaluatesIn.sum_list (values := [-3, 5]) (EvaluatesIn.lookup rfl) EvaluatesIn.constant rfl
example : EvaluatesIn .word program (fun _ => some (.ref 0))
    (.sumSequence (.name "xs") (.constant (.int 7))) [.list []] 16 (.scalar (.int 7)) [.list []] :=
  EvaluatesIn.sum_list (values := []) (EvaluatesIn.lookup rfl) EvaluatesIn.constant rfl

/-- Object-valued initial accumulators and non-sequence receivers have no tariff. -/
example : operation .word [.list []] .sumSequence [.ref 0, .ref 0] = none := rfl
example : operation .word [] .sumSequence [.scalar (.int 10), .scalar (.int 0)] = none := rfl

/-- Zero still formats as one character. The multi-digit case follows the same generator proof. -/
example : ∃ answer, EvaluatesIn .word program (fun _ => none)
    (DecimalSum.expression (.constant (.int 0))) [] 50 (.scalar (.int answer)) [] :=
  DecimalSum.evaluates 0 1 (by decide) (by decide) EvaluatesIn.constant
example : ∃ answer, EvaluatesIn .word program (fun _ => none)
    (DecimalSum.expression (.constant (.int 1234))) [] 122 (.scalar (.int answer)) [] :=
  DecimalSum.evaluates 1234 4 (by decide) (by decide) EvaluatesIn.constant
