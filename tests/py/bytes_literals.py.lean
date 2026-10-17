import «.formalsw».tests.py.«bytes_literals.py.ast»
import FormalSW

namespace tests.py.bytes_literals
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := BytesLiteralsAst.module

/-- Repetition truncates negative counts to zero, exactly as Python does. -/
theorem flags.result (n : Int) :
    ReturnsValue program "flags" [.int n] (.bytes (List.replicate n.toNat [1]).flatten) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.binary Evaluates.constant (Evaluates.lookup rfl) rfl

theorem flags.«Returns» (n : Int) : (function program "flags" [.int n]).Returns :=
  (flags.result n).returns

theorem reverse.«Returns» (n : Int) : (function program "reverse" [.int n]).Returns := by
  apply ReturnsValue.returns (value := .bytes ((List.replicate n.toNat [0, 255]).flatten.reverse))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.slice (stepValue := .int (-1))
  · exact .cons (Evaluates.binary Evaluates.constant (Evaluates.lookup rfl) rfl)
      (.cons Evaluates.constant (.cons Evaluates.constant
        (.cons (Evaluates.unary Evaluates.constant rfl) .nil)))
  · exact Strings.slice_reverse_bytes _

theorem heap_flags.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "heap_flags" [.int n]).Returns := by
  refine ⟨.bytes (List.replicate n.toNat [1]).flatten, Execution.finishes_of_observe (fuel := 40) ?_⟩
  rfl

theorem heap_flags.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "heap_flags" [.int n]).Supported :=
  (heap_flags.«Returns» n).supported

theorem first_byte.«Returns» (n : Int) : (function program "first_byte" [.int n]).Returns := by
  exact ⟨.int (255 + n), Execution.finishes_of_observe (fuel := 30) rfl⟩

theorem mixed_text.throws (n : Int) : (function program "mixed_text" [.int n]).Throws := by
  exact ⟨⟨"TypeError", []⟩, Execution.finishes_of_observe (fuel := 30) rfl⟩

end tests.py.bytes_literals
