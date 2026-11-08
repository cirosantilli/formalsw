import lang.py.FormalSW.HeapRuntimeCostSequences

/-! Scalar string and bytes access in the heap interpreter uses the same tariffs
as the scalar interpreter. Slices pay for copying; argument evaluation may
change the heap even though the final scalar operation does not. -/
namespace FormalSW.PyAst.HeapCalls.Runtime.EvaluatesIn

/-- Decimal parsing has linear character cost under fixed arithmetic. -/
theorem parse_string_word
    (argument : EvaluatesIn .word module env expression heap cost (.scalar (.string text)) middle)
    (parsed : Calls.integerConversion [.string text] = some (.ok (.int answer))) :
    EvaluatesIn .word module env (.builtinCall .int [expression]) heap (cost+text.length+4)
      (.scalar (.int answer)) middle := by
  have converted : primitive (.builtin .int) [.scalar (.string text)] middle =
      some (.ok (.scalar (.int answer)), middle) := by
    change scalarResult (Calls.integerConversion [.string text]) middle = _
    rw [parsed]
    rfl
  have run := builtin_single (builtin := .int) (work := text.length+1)
    (by intro h; cases h) (by intro h; cases h) argument converted rfl
  exact run.mono (by omega)

theorem scalar_slice
    (arguments : ArgumentsIn arithmetic module env 0
      [base, lower.getD (.constant .none), upper.getD (.constant .none), stride.getD (.constant .none)]
      heap budget [.scalar receiver, .scalar first, .scalar last, .scalar stepValue] middle)
    (evaluated : Mutable.getSlice (.scalar receiver) (.scalar first) (.scalar last) (.scalar stepValue) middle =
      some (.ok (.scalar answer), middle))
    (priced : Calls.Runtime.primitive arithmetic .slice [receiver, first, last, stepValue] = some work) :
    EvaluatesIn arithmetic module env (.subscript base (.slice lower upper stride)) heap
      (budget + work + 2) (.scalar answer) middle := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.subscript base (.slice lower upper stride)) env, stack, heap⟩ 1
      (argumentsState .slice env [] [base, lower.getD (.constant .none),
        upper.getD (.constant .none), stride.getD (.constant .none)] stack heap) := advance rfl rfl rfl
  have sliced : Reaches arithmetic module anchors
      ⟨.operation .slice [.scalar receiver, .scalar first, .scalar last, .scalar stepValue], stack, middle⟩
      (work+1) ⟨.value (.scalar answer), stack, middle⟩ :=
    advance (by simp [step, result, run, primitive, evaluated])
      (by simp [charge, operation, priced]) rfl
  exact ((initial.trans (arguments.reaches .slice anchors stack)).trans sliced).mono (by omega)

/-- A nonnegative string prefix, including evaluation of its receiver and bound. -/
theorem string_prefix_word {count : Nat}
    (receiver : EvaluatesIn .word module env base heap ca (.scalar (.string text)) middle)
    (bound : EvaluatesIn .word module env stop middle cb (.scalar (.int count)) afterBound) :
    EvaluatesIn .word module env (.subscript base (.slice none (some stop) none)) heap
      (ca+cb+text.length+22) (.scalar (.string (String.ofList (text.toList.take count)))) afterBound := by
  have sliced := Py.Builtin.Sequence.slice_prefix text.toList (count : Int)
  rw [Py.Builtin.Slice.prefixLength_nonnegative, ← List.take_eq_take_min] at sliced
  have converted : Strings.slice (.string text) .none (.int count) .none =
      .ok (.string (String.ofList (text.toList.take count))) := by
    change (match Py.Builtin.Sequence.slice text.toList { stop := some (count : Int) } with
      | .ok characters => Except.ok (Constant.string (String.ofList characters))
      | .error _ => Except.error ({ typeName := "ValueError", args := [] } : ExceptionObject)) = _
    rw [sliced]
  have copied : Mutable.getSlice (.scalar (.string text)) (.scalar .none) (.scalar (.int count))
      (.scalar .none) afterBound =
      some (.ok (.scalar (.string (String.ofList (text.toList.take count)))), afterBound) := by
    change (match Strings.slice (.string text) .none (.int count) .none with
      | .ok value => some (Except.ok (Mutable.Value.scalar value), afterBound)
      | .error error => some (Except.error error, afterBound)) = _
    rw [converted]
  have priced : Calls.Runtime.primitive .word .slice [.string text, .none, .int count, .none] =
      some (text.length+8) := by
    simp [Calls.Runtime.primitive, Calls.Runtime.argumentWork, PrimitiveWork.scalarSize, PrimitiveWork.integer]
    omega
  have run := scalar_slice (lower := none) (upper := some stop) (stride := none)
    (ArgumentsIn.cons receiver (ArgumentsIn.cons EvaluatesIn.constant
      (ArgumentsIn.cons bound (ArgumentsIn.cons EvaluatesIn.constant ArgumentsIn.nil)))) copied priced
  exact run.mono (by simp; omega)

theorem scalar_subscript (ordinary : ∀ a b c, index ≠ .slice a b c)
    (receiver : EvaluatesIn arithmetic module env base heap ca (.scalar value) middle)
    (position : EvaluatesIn arithmetic module env index middle cb (.scalar offset) afterIndex)
    (evaluated : Mutable.getItem (.scalar value) (.scalar offset) afterIndex =
      some (.ok (.scalar answer), afterIndex))
    (priced : Calls.Runtime.primitive arithmetic .subscript [value, offset] = some work) :
    EvaluatesIn arithmetic module env (.subscript base index) heap
      (ca + cb + work + 5) (.scalar answer) afterIndex := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.subscript base index) env, stack, heap⟩ 1
      (argumentsState .subscript env [] [base, index] stack heap) :=
    advance (by cases index <;> simp_all [step, argumentsState]) rfl rfl
  have args := (ArgumentsIn.cons receiver (ArgumentsIn.cons position ArgumentsIn.nil)).reaches
    (completed := []) .subscript anchors stack
  have read : Reaches arithmetic module anchors
      ⟨.operation .subscript [.scalar value, .scalar offset], stack, afterIndex⟩ (work+1)
      ⟨.value (.scalar answer), stack, afterIndex⟩ :=
    advance (by simp [step, result, run, primitive, evaluated])
      (by simp [charge, operation, priced]) rfl
  exact ((initial.trans args).trans read).mono (by simp; omega)

end FormalSW.PyAst.HeapCalls.Runtime.EvaluatesIn
