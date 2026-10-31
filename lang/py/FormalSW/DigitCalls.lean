import lang.py.FormalSW.HeapCalls

/-! Unicode digit tests retain the receiver and caller heap. -/
namespace FormalSW.PyAst.HeapCalls

variable {globals : Mutable.Globals} {module : Module} {env : Env}
  {base : Expr} {heap middle : Heap} {text : String}

@[simp] theorem primitive_isDigit_string (text : String) (heap : Heap) :
    primitive (.isDigit (.scalar (.string text))) [] heap =
      some (.ok (.scalar (.bool (Strings.isDigit text))), heap) := rfl

@[simp] theorem primitive_isDigit_bytes (bytes : List UInt8) (heap : Heap) :
    primitive (.isDigit (.scalar (.bytes bytes))) [] heap =
      some (.ok (.scalar (.bool (Py.Builtin.Bytes.isDigit bytes))), heap) := rfl

theorem primitive_isDigit_bytearray (heap : Heap) (address : Nat) (bytes : List UInt8)
    (found : heap[address]? = some (.bytearray bytes)) :
    primitive (.isDigit (.ref address)) [] heap =
      some (.ok (.scalar (.bool (Py.Builtin.Bytes.isDigit bytes))), heap) := by
  simp [primitive, found]

/-- Receiver effects run before Unicode digit classification, without further allocation. -/
theorem Evaluates.is_digit
    (receiver : Evaluates (globals := globals) module env base
      heap (.scalar (.string text)) middle)
    (localName : ∀ name, base = .name name → (env name).isSome = true) :
    Evaluates (globals := globals) module env (.call (.attribute base "isdigit") []) heap
      (.scalar (.bool (Strings.isDigit text))) middle := by
  intro anchors stack
  apply Reaches.next (following :=
    ⟨.expr base env, .methodReceiver "isdigit" [] env :: stack, heap⟩)
    (by cases base <;> simp_all [step])
  apply (receiver anchors _).trans
  apply Reaches.next (following :=
    argumentsState (.isDigit (.scalar (.string text))) env [] [] stack middle)
    (by simp [step, run, bindMethod])
  exact .next (by simp [argumentsState, step, result, run]) .refl

end FormalSW.PyAst.HeapCalls
