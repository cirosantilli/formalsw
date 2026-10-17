import FormalSW

open FormalSW.PyAst

private def _this_module : Module := ⟨[]⟩
private def low : Value := .int 1
private def high : Value := .int 2
private def text : Value := .string []

-- Both true and false comparison results count as successful returns.
example : Returns(low < high) := ⟨true, .done rfl⟩
example : Returns(high < low) := ⟨false, .done rfl⟩
example : Returns(low <= high) := ⟨true, .done rfl⟩
example : Returns(high <= low) := ⟨false, .done rfl⟩
example : Returns(high > low) := ⟨true, .done rfl⟩
example : Returns(low > high) := ⟨false, .done rfl⟩
example : Returns(high >= low) := ⟨true, .done rfl⟩
example : Returns(low >= high) := ⟨false, .done rfl⟩
example : Returns(low == low) := ⟨true, .done rfl⟩
example : Returns(low == high) := ⟨false, .done rfl⟩
example : Returns(low != high) := ⟨true, .done rfl⟩
example : Returns(low != low) := ⟨false, .done rfl⟩
example : Throws(low < text) := ⟨_, .done rfl⟩
example : Throws(low <= text) := ⟨_, .done rfl⟩
example : Throws(low > text) := ⟨_, .done rfl⟩
example : Throws(low >= text) := ⟨_, .done rfl⟩
example : Returns(low == text) := ⟨false, .done rfl⟩
example : Returns(low != text) := ⟨true, .done rfl⟩
example : Returns(((Value.int (1 + 1)) < high)) := ⟨false, .done rfl⟩

example (left right : Value) :
    Not Throws(left < right) ↔ ¬ Throws(left < right) := Iff.rfl
example (left right : Value) (h : Returns(left < right)) : Not Throws(left < right) :=
  (Execution.returns_iff_halts_not_throws _).mp h |>.2
example : (1 : Nat) < 2 := by decide

/-- error: expected a comparison using <, <=, >, >=, ==, or != -/
#guard_msgs in
#check Throws(True)

private def successful (_ : Nat) : Execution Bool := Execution.pure false
private def failing (_ : Nat) : Execution Bool := Execution.raise ⟨"Error", []⟩
private def unsupported (_ : Nat) : Execution Bool := Execution.unsupported
private def forever : Execution Bool := ⟨Unit, (), fun _ => .next ()⟩
private def binary (a b : Nat) : Execution Nat := Execution.pure (a + b)

example : Returns(successful(1 + 1)) := ⟨false, .done rfl⟩
example : Throws(failing(0)) := ⟨_, .done rfl⟩
example : Halts(failing(0)) := Execution.throws_halts ⟨_, .done rfl⟩
example : Returns(binary(1, 2)) := ⟨3, .done rfl⟩
example : diverges(forever()) := ⟨fun _ => True, trivial, fun _ _ => ⟨(), rfl, trivial⟩⟩
example : Not Halts(forever()) := Execution.diverges_not_halts
  ⟨fun _ => True, trivial, fun _ _ => ⟨(), rfl, trivial⟩⟩
example : Execution.observe forever 100 = .pending := rfl
example : Execution.observe (successful 0) 0 = .pending := rfl
-- Internal coverage failures remain detectable by the observer. The CLI rejects
-- requirements depending on unsupported source before accepting Lean proofs.
example : Execution.observe (unsupported 0) 1 = .unsupported := rfl

example (this_function : List Value → Execution (List Value)) (values : List Value) :
    Returns(this_function(values)) ↔ Halts(this_function(values)) ∧ Not Throws(this_function(values)) :=
  Execution.returns_iff_halts_not_throws _
example (this_function : Int → Execution Constant) (n : Int) :
    Throws(this_function(n)) → Halts(this_function(n)) := Execution.throws_halts
example (left right : Execution Constant) (h : left.Equiv right) :
    left.Returns ↔ right.Returns := h.returns_iff

-- An extra infinite loop must invalidate the recognized sorting program.
private def alteredSort : Module := ⟨[
  .functionDef "sort" [{ name := "values", annotation := some (.name "list") }]
    (some (.name "list"))
    (.whileDo (.constant (.bool true)) [.expr (.constant .none)] [] ::
      mergeSortBody "sort" "values")
]⟩
example : isMergeSortFunction alteredSort "sort" = false := by native_decide
example : (listFunction alteredSort "sort" []).observe 5 = .unsupported := by native_decide

-- Python treats booleans as integers in comparisons, including mixed equality.
example : scalarCompare .eq (.bool true) (.int 1) = some true := rfl
example : scalarCompare .notEq (.bool false) (.int 0) = some false := rfl
example : scalarCompare .lt (.bool false) (.bool true) = some true := rfl
