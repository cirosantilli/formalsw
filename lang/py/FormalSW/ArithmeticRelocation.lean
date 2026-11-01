import lang.py.FormalSW.MachineAttributes

/-! Scalar arithmetic and unary evaluation preserve runtime layouts. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem scalarResult_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (result : Option (Except ExceptionObject Constant)) :
    scalarResult result physical = (scalarResult result logical).map
      (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  cases result with
  | none => rfl
  | some outcome => cases outcome <;> rfl

theorem scalarResult_effect (heap after : Mutable.Heap) (result : Option (Except ExceptionObject Constant))
    (outcome : Except ExceptionObject Value)
    (executed : scalarResult result heap = some (outcome, after)) :
    after = heap ∧ ∀ value, outcome = .ok value → ∃ scalar, value = .scalar scalar := by
  cases result with
  | none => simp [scalarResult, Mutable.unsupported] at executed
  | some result =>
    cases result with
    | error exception =>
      have same : Except.error exception = outcome ∧ heap = after := by simpa [scalarResult] using executed
      exact ⟨same.2.symm, by intro value impossible; rw [← same.1] at impossible; cases impossible⟩
    | ok scalar =>
      have same : Except.ok (Mutable.Value.scalar scalar) = outcome ∧ heap = after := by simpa [scalarResult] using executed
      refine ⟨same.2.symm, ?_⟩
      intro value success
      exact ⟨scalar, (Except.ok.inj (same.1.trans success)).symm⟩

private theorem scalarResult_match (result : Option (Except ExceptionObject Constant)) :
    (match result with
      | some (.ok value) => pure (.scalar value)
      | some (.error exception) => throw exception
      | none => Mutable.unsupported) = scalarResult result := by
  cases result with
  | none => rfl
  | some outcome => cases outcome <;> rfl

private theorem binary_add_test (op : BinOp) : (op == .add) = (match op with | .add => true | _ => false) := by
  cases op <;> rfl

private theorem binary_mult_test (op : BinOp) : (op == .mult) = (match op with | .mult => true | _ => false) := by
  cases op <;> rfl

/-- The scalar fast paths agree, including Boolean coercion and string/bytes operations. -/
theorem binary_scalars (op : BinOp) (left right : Constant) :
    Mutable.binary op (.scalar left) (.scalar right) = scalarResult (scalarBinary op left right) := by
  cases op with
  | bitAnd => cases result : scalarBitAnd left right <;> simp [Mutable.binary, scalarBinary, scalarResult, result]
  | bitOr => cases result : scalarBitOr left right <;> simp [Mutable.binary, scalarBinary, scalarResult, result]
  | bitXor => cases result : scalarBitXor left right <;> simp [Mutable.binary, scalarBinary, scalarResult, result]
  | leftShift => cases result : scalarShiftLeft left right <;> simp [Mutable.binary, scalarBinary, scalarResult, result]
  | rightShift => cases result : scalarShiftRight left right <;> simp [Mutable.binary, scalarBinary, scalarResult, result]
  | add | sub | mult | pow | floorDiv | mod =>
    cases left <;> cases right <;>
      simp [Mutable.binary, scalarResult, scalarBinary, scalarNumber, Mutable.error, binary_add_test, binary_mult_test]
    all_goals exact scalarResult_match _

theorem binary_scalars_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (op : BinOp) (left right : Constant) :
    Mutable.binary op (.scalar left) (.scalar right) physical =
      (Mutable.binary op (.scalar left) (.scalar right) logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  rw [binary_scalars]
  exact scalarResult_relocates logical physical rename _

theorem truth_total (heap : Mutable.Heap) (value : Value) (inside : value.edge.Within heap.length) :
    ∃ truth, Mutable.truth value heap = some (.ok truth, heap) := by
  cases value with
  | scalar scalar => exact ⟨scalarTruth scalar, rfl⟩
  | ref address =>
    have found : heap[address]? = some heap[address] := List.getElem?_eq_getElem inside
    cases object : heap[address] with
    | list items | tuple items | bytearray items | set items | keySet items | dict items | keyDict items =>
      exact ⟨!items.isEmpty, by simp [Mutable.truth, found, object]⟩
    | «instance» origin name fields | dataInstance origin name frozen declared fields =>
      exact ⟨true, by simp [Mutable.truth, found, object]⟩

theorem unary_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (op : UnaryOp) (value : Value)
    (inside : value.edge.Within logical.length) :
    unary op (relocateValue rename value) physical = (unary op value logical).map
      (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  cases op with
  | not =>
    obtain ⟨truth, tested⟩ := truth_total logical value inside
    have paired := layout.truth value inside
    simp only [unary, Mutable.eval_bind, paired, tested, Option.map_some, Except.map]
    rfl
  | uSub =>
    cases value with
    | scalar scalar => exact scalarResult_relocates logical physical rename _
    | ref address => rfl

theorem unary_effect (heap after : Mutable.Heap) (op : UnaryOp) (value : Value)
    (inside : value.edge.Within heap.length) (outcome : Except ExceptionObject Value)
    (executed : unary op value heap = some (outcome, after)) :
    after = heap ∧ ∀ returned, outcome = .ok returned → ∃ scalar, returned = .scalar scalar := by
  cases op with
  | not =>
    obtain ⟨truth, tested⟩ := truth_total heap value inside
    have same : Except.ok (Mutable.Value.scalar (.bool (!truth))) = outcome ∧ heap = after := by
      simpa [unary, tested, Mutable.eval_bind] using executed
    refine ⟨same.2.symm, ?_⟩
    intro returned success
    exact ⟨.bool (!truth), (Except.ok.inj (same.1.trans success)).symm⟩
  | uSub =>
    cases value with
    | scalar scalar => exact scalarResult_effect heap after _ outcome executed
    | ref address =>
      have same : Except.error {typeName := "TypeError", args := []} = outcome ∧ heap = after := by
        simpa [unary, Mutable.error] using executed
      exact ⟨same.2.symm, by intro returned impossible; rw [← same.1] at impossible; cases impossible⟩

end FormalSW.PyAst.HeapCalls.Relocation
