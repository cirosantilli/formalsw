import lang.py.FormalSW.HeapRuntimeCostStrings

open FormalSW.PyAst HeapCalls HeapCalls.Runtime
private def program : Module := { body := [] }

/-- Parsing scans all characters even when integer arithmetic has fixed cost. -/
example (text : String) : Calls.Runtime.primitive .word (.builtin .int) [.string text] =
    some (text.length+1) := rfl
example (text : String) : Calls.Runtime.primitive .bits (.builtin .int) [.string text] =
    some ((text.length+1)^2) := by simp [Calls.Runtime.primitive, PrimitiveWork.decimalInput, Nat.pow_succ]
example (bytes : List UInt8) : operation .word [] (.builtin .int) [.scalar (.bytes bytes)] =
    some (bytes.length+1) := rfl
example (bytes : List UInt8) : operation .bits [] (.builtin .int) [.scalar (.bytes bytes)] =
    some ((bytes.length+1)^2) := by
  simp [operation, scalarValues, Calls.Runtime.primitive, PrimitiveWork.decimalInput, Nat.pow_succ]

/-- Signs, whitespace and separators are included in the scanned length. -/
example (heap : Heap) : EvaluatesIn .word program (fun _ => none)
    (.builtinCall .int [.constant (.string " -12_345 ")]) heap 14 (.scalar (.int (-12345))) heap := by
  apply EvaluatesIn.builtin_single (ca := 1) (work := 10) (by intro h; cases h) (by intro h; cases h)
  · exact EvaluatesIn.constant
  · rfl
  · rfl

/-- Both backends charge the same source-length-dependent copy. -/
example (text : String) (stop : Int) (heap : Heap) :
    operation .word heap .slice [.scalar (.string text), .scalar .none,
      .scalar (.int stop), .scalar .none] = some (text.length+8) := by
  simp [operation, Calls.Runtime.primitive, Calls.Runtime.argumentWork,
    PrimitiveWork.scalarSize, PrimitiveWork.integer]
  omega

/-- A prefix copies its selected characters without changing existing objects. -/
example (heap : Heap) : EvaluatesIn .word program (fun _ => none)
    (.subscript (.constant (.string "12345")) (.slice none (some (.constant (.int 3))) none))
    heap 29 (.scalar (.string "123")) heap := by
  apply EvaluatesIn.scalar_slice (budget := 14) (work := 13)
  · exact ArgumentsIn.cons EvaluatesIn.constant (ArgumentsIn.cons EvaluatesIn.constant
      (ArgumentsIn.cons EvaluatesIn.constant (ArgumentsIn.cons EvaluatesIn.constant ArgumentsIn.nil)))
  · rfl
  · rfl

/-- Negative bounds and reverse strides follow Python slicing. -/
example (heap : Heap) : EvaluatesIn .word program (fun _ => none)
    (.subscript (.constant (.string "abcde"))
      (.slice (some (.constant (.int (-2)))) none (some (.constant (.int (-1))))))
    heap 29 (.scalar (.string "dcba")) heap := by
  apply EvaluatesIn.scalar_slice (budget := 14) (work := 13)
  · exact ArgumentsIn.cons EvaluatesIn.constant (ArgumentsIn.cons EvaluatesIn.constant
      (ArgumentsIn.cons EvaluatesIn.constant (ArgumentsIn.cons EvaluatesIn.constant ArgumentsIn.nil)))
  · rfl
  · rfl

/-- An empty slice still pays for bound normalization and conservative copying. -/
example (heap : Heap) : EvaluatesIn .word program (fun _ => none)
    (.subscript (.constant (.string "12345")) (.slice none (some (.constant (.int 0))) none))
    heap 29 (.scalar (.string "")) heap := by
  apply EvaluatesIn.scalar_slice (budget := 14) (work := 13)
  · exact ArgumentsIn.cons EvaluatesIn.constant (ArgumentsIn.cons EvaluatesIn.constant
      (ArgumentsIn.cons EvaluatesIn.constant (ArgumentsIn.cons EvaluatesIn.constant ArgumentsIn.nil)))
  · rfl
  · rfl

example (heap : Heap) : EvaluatesIn .word program (fun _ => none)
    (.subscript (.constant (.bytes [65, 66, 67])) (.constant (.int (-1))))
    heap 9 (.scalar (.int 67)) heap := by
  apply EvaluatesIn.scalar_subscript (ca := 1) (cb := 1) (work := 2)
  · intro a b c h; cases h
  · exact EvaluatesIn.constant
  · exact EvaluatesIn.constant
  · rfl
  · rfl

/-- Numeric scalars cannot silently acquire sequence tariffs. -/
example : operation .word [] .slice
    [.scalar (.int 123), .scalar .none, .scalar .none, .scalar .none] = none := rfl
example : operation .word [] .subscript [.scalar (.int 123), .scalar (.int 0)] = none := rfl

/-- Bit arithmetic accounts for wide indices even when the source is short. -/
example : operation .bits [] .subscript [.scalar (.string "abc"), .scalar (.int 1024)] = some 12 := rfl
