import lang.py.FormalSW.CallsRuntimeCost

open FormalSW.PyAst Calls Calls.Runtime

/-- Generated shape of max(range(1, limit + 1), key=score).
The source key performs arithmetic, and equal scores retain the first index. -/
private def program : Module := { body := [
  .functionDef "score" [⟨"n", none, none⟩] none
    [.return (.binOp (.name "n") .mod (.constant (.int 2)))],
  .functionDef "solve" [⟨"limit", none, none⟩] none
    [.return (.extremumRange true
      [.constant (.int 1), .binOp (.name "limit") .add (.constant (.int 1))] "score")]] }

private theorem maximum_word : RuntimeCost.Finishes (Calls.step program)
    (charge .word program) ⟨.invoke "solve" [.int 3], []⟩ 71 (.ok (.int 1)) := by
  have run : RuntimeCost.Reaches (Calls.step program) (charge .word program)
      ⟨.invoke "solve" [.int 3], []⟩ 70 ⟨.value (.int 1), []⟩ := by
    repeat first | exact RuntimeCost.Reaches.refl | runtime_step
  exact run.finishes (.done rfl rfl)

private theorem maximum_bits : RuntimeCost.Finishes (Calls.step program)
    (charge .bits program) ⟨.invoke "solve" [.int 3], []⟩ 99 (.ok (.int 1)) := by
  have run : RuntimeCost.Reaches (Calls.step program) (charge .bits program)
      ⟨.invoke "solve" [.int 3], []⟩ 98 ⟨.value (.int 1), []⟩ := by
    repeat first | exact RuntimeCost.Reaches.refl | runtime_step
  exact run.finishes (.done rfl rfl)

example : RuntimeCost.TimeBound (Calls.function program "solve" [.int 3])
    (charge .word program) 71 := ⟨71, .ok (.int 1), maximum_word, Nat.le_refl _⟩
example : RuntimeCost.TimeBound (Calls.function program "solve" [.int 3])
    (charge .bits program) 99 := ⟨99, .ok (.int 1), maximum_bits, Nat.le_refl _⟩

/-- A descending minimum executes the same key but reverses the score ordering. -/
example : RuntimeCost.Finishes (Calls.step program) (charge .word program)
    ⟨.startExtremum false "score" [.int 3, .int 0, .int (-1)], []⟩ 58 (.ok (.int 2)) := by
  have run : RuntimeCost.Reaches (Calls.step program) (charge .word program)
      ⟨.startExtremum false "score" [.int 3, .int 0, .int (-1)], []⟩
      57 ⟨.value (.int 2), []⟩ := by
    repeat first | exact RuntimeCost.Reaches.refl | runtime_step
  exact run.finishes (.done rfl rfl)

/-- Setup and even an exhausted range pay for wide integers in the bit model. -/
example : charge .word program
    ⟨.startExtremum true "score" [.bool true, .int (2^100)], []⟩ = some 3 := by decide
example : charge .bits program
    ⟨.startExtremum true "score" [.bool true, .int (2^100)], []⟩ = some 103 := by decide
example : charge .bits program
    ⟨.extremumLoop ⟨true, "score", 2^100, 1⟩ (2^100) none, []⟩ = some 204 := by decide
example : RuntimeCost.Finishes (Calls.step program) (charge .word program)
    ⟨.extremumLoop ⟨true, "score", 4, 1⟩ 4 none, []⟩ 4
    (.error { typeName := "ValueError", args := [] }) := .done rfl rfl
example : RuntimeCost.Finishes (Calls.step program) (charge .bits program)
    ⟨.startExtremum true "score" [.int 1, .int 4, .int 0], []⟩ 6
    (.error { typeName := "ValueError", args := [] }) := .done rfl rfl

/-- Advancing an index pays for its width even before any key comparison. -/
example : charge .word program
    ⟨.value .none, [.extremumKey ⟨true, "score", 0, 1⟩ (2^100) none]⟩ = some 2 := by decide
example : charge .bits program
    ⟨.value .none, [.extremumKey ⟨true, "score", 0, 1⟩ (2^100) none]⟩ = some 103 := by decide

/-- Score widths are independent of the range index width. -/
example : charge .word program
    ⟨.value (.int (2^100)), [.extremumKey ⟨true, "score", 4, 1⟩ 1
      (some (0, .int (2^100)))]⟩ = some 4 := by decide
example : charge .bits program
    ⟨.value (.int (2^100)), [.extremumKey ⟨true, "score", 4, 1⟩ 1
      (some (0, .int (2^100)))]⟩ = some 205 := by decide

/-- Long string keys cost more under both arithmetic policies. -/
example (arithmetic : PrimitiveWork.Arithmetic) : charge arithmetic program
    ⟨.value (.string "aa"), [.extremumKey ⟨true, "score", 4, 1⟩ 1
      (some (0, .string "aa"))]⟩ =
    some (1 + (PrimitiveWork.integerBinary arithmetic .add 1 1).getD 0 + 6) := by
  cases arithmetic <;> decide
example (arithmetic : PrimitiveWork.Arithmetic) : charge arithmetic program
    ⟨.value (.string "aaaaaaaaaaaaaaaa"), [.extremumKey ⟨true, "score", 4, 1⟩ 1
      (some (0, .string "aaaaaaaaaaaaaaaa"))]⟩ =
    some (1 + (PrimitiveWork.integerBinary arithmetic .add 1 1).getD 0 + 34) := by
  cases arithmetic <;> decide
example : charge .word program
    ⟨.value (.bytes [65, 66]), [.extremumKey ⟨false, "score", 0, -1⟩ 1
      (some (2, .bytes [65, 67]))]⟩ = some 8 := by decide

/-- Unsupported indices and score pairs cannot borrow a unit tariff. -/
example (arithmetic : PrimitiveWork.Arithmetic) : charge arithmetic program
    ⟨.startExtremum true "score" [.string "3"], []⟩ = none := by
  cases arithmetic <;> rfl
example (arithmetic : PrimitiveWork.Arithmetic) : charge arithmetic program
    ⟨.value .none, [.extremumKey ⟨true, "score", 4, 1⟩ 1
      (some (0, .none))]⟩ = none := by
  cases arithmetic <;> rfl
example : charge .word program
    ⟨.value (.string "3"), [.extremumKey ⟨true, "score", 4, 1⟩ 1
      (some (0, .int 3))]⟩ = none := rfl
example (cost : Nat) (answer : Except ExceptionObject Constant) :
    ¬ RuntimeCost.Finishes (Calls.step program) (charge .word program)
    ⟨.value .none, [.extremumKey ⟨true, "score", 4, 1⟩ 1
      (some (0, .none))]⟩ cost answer :=
  RuntimeCost.Finishes.impossible_of_missing rfl
