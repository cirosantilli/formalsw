import lang.py.FormalSW.HeapRuntimeCostListRepetition

namespace ListRepetitionRuntimeRegression
open FormalSW.PyAst HeapCalls HeapCalls.Runtime PrimitiveWork
private def program : Module := { body := [] }

/-- Repetition copies aliases to the original object, without cloning it. -/
example : EvaluatesIn .word program (fun _ => some (.ref 0))
    (.binOp (.name "xs") .mult (.constant (.int 3))) [.list [.ref 0]] 13
    (.ref 1) [.list [.ref 0], .list [.ref 0, .ref 0, .ref 0]] := by
  exact EvaluatesIn.list_repeat (items := [.ref 0]) (count := 3)
    (EvaluatesIn.lookup rfl) EvaluatesIn.constant rfl

/-- A negative count produces a fresh empty list and retains the receiver. -/
example : EvaluatesIn .word program (fun _ => some (.ref 0))
    (.binOp (.name "xs") .mult (.constant (.int (-3)))) [.list [.ref 0]] 7
    (.ref 1) [.list [.ref 0], .list []] := by
  exact EvaluatesIn.list_repeat (items := [.ref 0]) (count := -3)
    (EvaluatesIn.lookup rfl) EvaluatesIn.constant rfl

/-- Empty output still charges the bit width of the count. -/
example : charge .bits program
    ⟨.value (.scalar (.int (2^100))), [.binaryRight .mult (.ref 0) false], [.list []]⟩ = some 103 := by decide
example : charge .word program
    ⟨.value (.scalar (.int (2^100))), [.binaryRight .mult (.ref 0) false], [.list []]⟩ = some 3 := by decide

/-- Reflected multiplication and booleans use the same reference-copy tariff. -/
example : charge .word program
    ⟨.value (.ref 0), [.binaryRight .mult (.scalar (.int 3)) false], [.list [.ref 0]]⟩ = some 6 := rfl
example : charge .word program
    ⟨.value (.scalar (.bool true)), [.binaryRight .mult (.ref 0) false], [.list [.ref 0]]⟩ = some 4 := rfl

/-- Buffer repetition retains its existing tariff; other protocols stay unsupported. -/
example : charge .word program
    ⟨.value (.scalar (.int 3)), [.binaryRight .mult (.ref 0) false], [.bytearray [1, 2]]⟩ = some 9 := rfl
example : charge .word program
    ⟨.value (.scalar (.int 3)), [.binaryRight .mult (.ref 0) false], [.tuple []]⟩ = none := rfl
example : charge .word program
    ⟨.value (.scalar (.int 3)), [.binaryRight .mult (.ref 0) true], [.list []]⟩ = none := rfl

#print axioms EvaluatesIn.list_repeat
end ListRepetitionRuntimeRegression
