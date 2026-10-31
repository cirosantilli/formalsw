import «.formalsw».tests.py.«string_repr.py.ast»
import FormalSW

namespace tests.py.string_repr
open FormalSW.PyAst
private abbrev program := StringReprAst.module
private def answer (text : String) : String := "Invalid attempt: " ++ Strings.reprText text

private theorem reference.result (text : String) :
    Calls.ReturnsValue program "reference" [.string text] (.string (answer text)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  exact Calls.Evaluates.binary Calls.Evaluates.constant
    (Calls.Evaluates.repr (Calls.Evaluates.lookup rfl)) rfl

private theorem solve.result (text : String) :
    Calls.ReturnsValue program "solve" [.string text] (.string (answer text)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  apply Calls.Evaluates.binary
  · exact Calls.Evaluates.binary Calls.Evaluates.constant Calls.Evaluates.constant rfl
  · exact Calls.Evaluates.repr (Calls.Evaluates.lookup rfl)
  · rfl

theorem reference.«Returns» (text : String) :
    (Calls.function program "reference" [.string text]).Returns := (reference.result text).returns

theorem reference.«Supported» (text : String) :
    (Calls.function program "reference" [.string text]).Supported :=
  (reference.«Returns» text).supported

theorem solve.«Returns» (text : String) :
    (Calls.function program "solve" [.string text]).Returns := (solve.result text).returns

theorem solve.«Equiv(reference)» (text : String) :
    (Calls.function program "solve" [.string text]).Equiv
      (Calls.function program "reference" [.string text]) :=
  Calls.ReturnsValue.equiv (solve.result text) (reference.result text)

theorem solve.«Supported» :
    (∀ text : String, (Calls.function program "solve" [.string text]).Supported) ∧
      (∀ text : String, (Calls.function program "reference" [.string text]).Supported) :=
  ⟨fun text => (solve.«Returns» text).supported, reference.«Supported»⟩

end tests.py.string_repr
