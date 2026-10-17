import «.formalsw».tests.py.«strings.py.ast»
import FormalSW

namespace tests.py.strings
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := StringsAst.module

theorem stringify.result (n : Int) :
    ReturnsValue program "stringify" [.int n] (.string (toString n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.builtin (values := [.int n])
  · exact .cons (Evaluates.lookup rfl) .nil
  · rfl

theorem stringify.«Returns» (n : Int) : (Calls.function program "stringify" [.int n]).Returns :=
  (stringify.result n).returns

theorem reverse.result (s : String) :
    ReturnsValue program "reverse" [.string s] (.string (String.ofList s.toList.reverse)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.slice (stepValue := .int (-1))
  · exact .cons (Evaluates.lookup rfl) (.cons Evaluates.constant (.cons Evaluates.constant
      (.cons (Evaluates.unary Evaluates.constant rfl) .nil)))
  · exact Strings.slice_reverse s

theorem reverse.«Returns» (s : String) : (Calls.function program "reverse" [.string s]).Returns :=
  (reverse.result s).returns

theorem double_reverse.«Equiv(identity)» (s : String) :
    (Calls.function program "double_reverse" [.string s]).Equiv
      (scalarFunction program "identity" [.string s]) := by
  have left : ReturnsValue program "double_reverse" [.string s] (.string s) := by
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.call (.cons (Evaluates.call (.cons (Evaluates.lookup rfl) .nil)
      (reverse.result s)) .nil)
    simpa using reverse.result (String.ofList s.toList.reverse)
  have right : Finishes (scalarFunction program "identity" [.string s]).step
      (scalarFunction program "identity" [.string s]).initial (.ok (.string s)) :=
    Execution.finishes_of_observe (fuel := 5) rfl
  intro result
  constructor
  · intro h
    rw [h.unique left.finishes]
    exact right
  · intro h
    rw [h.unique right]
    exact left.finishes

theorem palindrome.«Returns» (n : Int) : (Calls.function program "palindrome" [.int n]).Returns := by
  apply ReturnsValue.returns (value := .bool (decide (toString n = String.ofList (toString n).toList.reverse)))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := .string (toString n))
  · apply Evaluates.builtin (values := [.int n])
    · exact .cons (Evaluates.lookup rfl) .nil
    · rfl
  · apply BlockReturns.return_value
    apply Evaluates.compare (Evaluates.lookup rfl)
    · apply Evaluates.slice
      · exact .cons (Evaluates.lookup rfl) (.cons Evaluates.constant (.cons Evaluates.constant
          (.cons (Evaluates.unary Evaluates.constant rfl) .nil)))
      · exact Strings.slice_reverse (toString n)
    · simp [scalarCompare]

theorem unicode.«Returns» (n : Int) : (Calls.function program "unicode" [.int n]).Returns := by
  refine ⟨.string "é😺ZéZ😺éA", ?_⟩
  exact Execution.finishes_of_observe (fuel := 150) rfl

theorem scalar_conversions.«Returns» (n : Int) :
    (Calls.function program "scalar_conversions" [.int n]).Returns := by
  refine ⟨.string "TrueFalseNonex", ?_⟩
  exact Execution.finishes_of_observe (fuel := 150) rfl

theorem helper_bound.«Equiv(reverse)» (s : String) :
    (Calls.function program "helper_bound" [.string s]).Equiv
      (Calls.function program "reverse" [.string s]) := by
  apply ReturnsValue.equiv (right := reverse.result s)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.slice (stepValue := .int (-1))
  · apply Evaluates.Arguments.cons (Evaluates.lookup rfl)
    apply Evaluates.Arguments.cons Evaluates.constant
    apply Evaluates.Arguments.cons Evaluates.constant
    apply Evaluates.Arguments.cons _ .nil
    apply Evaluates.call (.cons Evaluates.constant .nil)
    apply BlockReturns.function rfl rfl
    exact BlockReturns.return_value (Evaluates.unary Evaluates.constant rfl)
  · exact Strings.slice_reverse s

theorem bad_step.«Throws» : ∃ n : Int, (Calls.function program "bad_step" [.int n]).Throws := by
  refine ⟨0, { typeName := "ValueError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 100) rfl

theorem bad_index.«Throws» : ∃ n : Int, (Calls.function program "bad_index" [.int n]).Throws := by
  refine ⟨0, { typeName := "IndexError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 100) rfl

theorem ordered_bounds.«Throws» : ∃ n : Int, (Calls.function program "ordered_bounds" [.int n]).Throws := by
  refine ⟨0, { typeName := "ZeroDivisionError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 100) rfl

theorem step_before_bound.«Throws» : ∃ n : Int, (Calls.function program "step_before_bound" [.int n]).Throws := by
  refine ⟨0, { typeName := "ValueError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 100) rfl

theorem receiver_before_bounds.«Throws» : ∃ n : Int, (Calls.function program "receiver_before_bounds" [.int n]).Throws := by
  refine ⟨0, { typeName := "ZeroDivisionError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 100) rfl

end tests.py.strings
