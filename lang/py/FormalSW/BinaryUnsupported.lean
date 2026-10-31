import lang.py.FormalSW.BinaryDispatchRelocation

/-! Unsupported binary dispatch is independent of private allocation layouts. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

theorem allocateTuple_supported (heap : Heap) (items : List Value) : Mutable.allocateTuple items heap ≠ none := by
  by_cases empty : items.isEmpty = true
  · cases found : heap.findIdx? (fun object => decide (object = .tuple [])) <;>
      simp [Mutable.allocateTuple, empty, found, Except.map]
  · simp [Mutable.allocateTuple, empty, Except.map]

private def binOpDecidableEq : DecidableEq BinOp := fun left right => by
  cases left <;> cases right <;> first
    | exact isTrue rfl
    | exact isFalse (by intro same; cases same)

private theorem binOp_beq (left right : BinOp) :
    (left == right) = @decide (left = right) (binOpDecidableEq left right) := by
  cases left <;> cases right <;> rfl

variable {logical physical : Heap} {rename : Nat → Nat}

theorem RuntimeLayout.binary_ref_scalar_unsupported (layout : RuntimeLayout logical physical rename)
    (op : BinOp) (address : Nat) (object : Object) (right : Constant)
    (found : logical[address]? = some object) :
    Mutable.binary op (.ref (rename address)) (.scalar right) physical = none ↔
      Mutable.binary op (.ref address) (.scalar right) logical = none := by
  have moved := layout.lookup address _ found
  cases right <;> cases op <;>
    simp [Mutable.binary, Mutable.invalidBinary, binOp_beq, found, moved, error, unsupported]
  all_goals cases object <;>
    simp [relocateObject, Mutable.allocate, Mutable.allocateBuffer, Mutable.array, found, moved,
      error, unsupported, Except.map]

  all_goals (repeat' split) <;> simp_all [allocateTuple_supported]

theorem RuntimeLayout.binary_scalar_ref_unsupported (layout : RuntimeLayout logical physical rename)
    (op : BinOp) (left : Constant) (address : Nat) (object : Object)
    (found : logical[address]? = some object) :
    Mutable.binary op (.scalar left) (.ref (rename address)) physical = none ↔
      Mutable.binary op (.scalar left) (.ref address) logical = none := by
  have moved := layout.lookup address _ found
  cases left <;> cases op <;>
    simp [Mutable.binary, Mutable.invalidBinary, binOp_beq, found, moved, error, unsupported]
  all_goals cases object <;>
    simp [relocateObject, Mutable.allocate, Mutable.allocateBuffer, Mutable.array, found, moved,
      error, Except.map]

  all_goals (repeat' split) <;> simp_all [allocateTuple_supported]

theorem RuntimeLayout.binary_refs_unsupported (layout : RuntimeLayout logical physical rename)
    (op : BinOp) (left right : Nat) (leftObject rightObject : Object)
    (leftFound : logical[left]? = some leftObject) (rightFound : logical[right]? = some rightObject) :
    Mutable.binary op (.ref (rename left)) (.ref (rename right)) physical = none ↔
      Mutable.binary op (.ref left) (.ref right) logical = none := by
  have first := layout.lookup left _ leftFound
  have second := layout.lookup right _ rightFound
  cases op with
  | sub =>
    exact layout.setDifference_unsupported left right false
      (List.getElem?_eq_some_iff.mp leftFound).1 (List.getElem?_eq_some_iff.mp rightFound).1
  | bitOr =>
    exact layout.setUnion_unsupported left right false
      (List.getElem?_eq_some_iff.mp leftFound).1 (List.getElem?_eq_some_iff.mp rightFound).1
  | _ =>
    simp [Mutable.binary, Mutable.invalidBinary, binOp_beq, leftFound, rightFound, first, second, error, unsupported]
    all_goals cases leftObject <;> cases rightObject <;>
      simp [relocateObject, Mutable.allocate, Mutable.allocateBuffer, Mutable.array, leftFound, rightFound, first, second,
        error, unsupported, Except.map]

    all_goals (repeat' split) <;> simp_all [allocateTuple_supported]

theorem RuntimeLayout.binary_unsupported (layout : RuntimeLayout logical physical rename)
    (op : BinOp) (left right : Value) (leftInside : left.edge.Within logical.length)
    (rightInside : right.edge.Within logical.length) :
    Mutable.binary op (relocateValue rename left) (relocateValue rename right) physical = none ↔
      Mutable.binary op left right logical = none := by
  cases left with
  | scalar left =>
    cases right with
    | scalar right =>
      simp only [relocateValue, HeapCalls.Relocation.binary_scalars]
      cases scalarBinary op left right with
      | none => rfl
      | some outcome => cases outcome <;> simp [HeapCalls.scalarResult]
    | ref right =>
      exact layout.binary_scalar_ref_unsupported op left right logical[right] (List.getElem?_eq_getElem rightInside)
  | ref left =>
    cases right with
    | scalar right =>
      exact layout.binary_ref_scalar_unsupported op left logical[left] right (List.getElem?_eq_getElem leftInside)
    | ref right =>
      exact layout.binary_refs_unsupported op left right logical[left] logical[right]
        (List.getElem?_eq_getElem leftInside) (List.getElem?_eq_getElem rightInside)

theorem inplace_mult_list_supported (heap : Heap) (address : Nat) (items : List Value) (right : Value)
    (found : heap[address]? = some (.list items)) :
    HeapCalls.inplace .mult (.ref address) right heap ≠ none := by
  rw [HeapCalls.Relocation.inplace_mult_list_value_eval heap address items right found]
  cases right with
  | ref other => simp [Mutable.integer, error, eval_bind]
  | scalar scalar => cases scalar <;> simp [Mutable.integer, error, eval_bind, Except.map]

theorem inplace_mult_buffer_supported (heap : Heap) (address : Nat) (bytes : List UInt8) (right : Value)
    (found : heap[address]? = some (.bytearray bytes)) :
    HeapCalls.inplace .mult (.ref address) right heap ≠ none := by
  rw [inplace_mult_buffer_eval heap address bytes right found]
  cases right with
  | ref other => simp [Mutable.integer, error, eval_bind]
  | scalar scalar => cases scalar <;> simp [Mutable.integer, storeBufferResult, error, eval_bind, Except.map]

theorem RuntimeLayout.inplace_add_buffer_unsupported (layout : RuntimeLayout logical physical rename)
    (address : Nat) (bytes : List UInt8) (right : Value) (found : logical[address]? = some (.bytearray bytes))
    (rightInside : right.edge.Within logical.length) :
    HeapCalls.inplace .add (.ref (rename address)) (relocateValue rename right) physical = none ↔
      HeapCalls.inplace .add (.ref address) right logical = none := by
  rw [inplace_add_buffer_eval logical address bytes right found,
    inplace_add_buffer_eval physical (rename address) bytes (relocateValue rename right) (layout.lookup _ _ found)]
  have paired := layout.bufferOperand (some address) right (by
    intro other same
    cases same
    exact (List.getElem?_eq_some_iff.mp found).1) rightInside
  simp only [Option.map_some] at paired
  cases read : Relocation.bufferOperand (some address) right logical with
  | none => simp [eval_bind, paired, read]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    cases outcome <;> simp [eval_bind, paired, read, storeBufferResult, Except.map]

theorem RuntimeLayout.inplaceBinary_unsupported (layout : RuntimeLayout logical physical rename)
    (op : BinOp) (left right : Value) (leftInside : left.edge.Within logical.length)
    (rightInside : right.edge.Within logical.length) :
    Mutable.inplaceBinary op (relocateValue rename left) (relocateValue rename right) physical = none ↔
      Mutable.inplaceBinary op left right logical = none := by
  cases op with
  | sub =>
    cases left <;> cases right <;> first
      | exact layout.setDifference_unsupported _ _ true leftInside rightInside
      | exact layout.binary_unsupported .sub _ _ leftInside rightInside
  | bitOr =>
    cases left <;> cases right <;> first
      | exact layout.setUnion_unsupported _ _ true leftInside rightInside
      | exact layout.binary_unsupported .bitOr _ _ leftInside rightInside
  | add => exact layout.binary_unsupported .add left right leftInside rightInside
  | mult => exact layout.binary_unsupported .mult left right leftInside rightInside
  | bitAnd => exact layout.binary_unsupported .bitAnd left right leftInside rightInside
  | bitXor => exact layout.binary_unsupported .bitXor left right leftInside rightInside
  | leftShift => exact layout.binary_unsupported .leftShift left right leftInside rightInside
  | rightShift => exact layout.binary_unsupported .rightShift left right leftInside rightInside
  | pow => exact layout.binary_unsupported .pow left right leftInside rightInside
  | floorDiv => exact layout.binary_unsupported .floorDiv left right leftInside rightInside
  | mod => exact layout.binary_unsupported .mod left right leftInside rightInside

theorem RuntimeLayout.inplace_unsupported (layout : RuntimeLayout logical physical rename)
    (op : BinOp) (left right : Value) (leftInside : left.edge.Within logical.length)
    (rightInside : right.edge.Within logical.length) :
    HeapCalls.inplace op (relocateValue rename left) (relocateValue rename right) physical = none ↔
      HeapCalls.inplace op left right logical = none := by
  cases left with
  | scalar scalar => exact layout.binary_unsupported op (.scalar scalar) right leftInside rightInside
  | ref address =>
    change HeapCalls.inplace op (.ref (rename address)) (relocateValue rename right) physical = none ↔
      HeapCalls.inplace op (.ref address) right logical = none
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem leftInside
    have moved := layout.lookup address _ found
    cases object : logical[address] with
    | list items =>
      have first : logical[address]? = some (.list items) := by simpa only [object] using found
      have second : physical[rename address]? = some (.list (items.map (relocateValue rename))) := layout.lookup _ _ first
      by_cases added : op = .add
      · subst op
        exact layout.inplace_add_list_unsupported address items right first rightInside
      · by_cases multiplied : op = .mult
        · subst op
          exact iff_of_false (inplace_mult_list_supported physical (rename address) _ (relocateValue rename right) second)
            (inplace_mult_list_supported logical address items right first)
        · rw [inplace_list_fallback logical address items op right first added multiplied,
            inplace_list_fallback physical (rename address) _ op (relocateValue rename right) second added multiplied]
          exact layout.binary_unsupported op (.ref address) right leftInside rightInside
    | bytearray bytes =>
      have first : logical[address]? = some (.bytearray bytes) := by simpa only [object] using found
      have second : physical[rename address]? = some (.bytearray bytes) := layout.lookup _ _ first
      by_cases added : op = .add
      · subst op
        exact layout.inplace_add_buffer_unsupported address bytes right first rightInside
      · by_cases multiplied : op = .mult
        · subst op
          exact iff_of_false (inplace_mult_buffer_supported physical (rename address) bytes (relocateValue rename right) second)
            (inplace_mult_buffer_supported logical address bytes right first)
        · rw [inplace_buffer_fallback logical address bytes op right first added multiplied,
            inplace_buffer_fallback physical (rename address) bytes op (relocateValue rename right) second added multiplied]
          exact layout.binary_unsupported op (.ref address) right leftInside rightInside
    | set items =>
      simpa [HeapCalls.inplace, found, moved, object, relocateObject, relocateValue] using
        layout.inplaceBinary_unsupported op (.ref address) right leftInside rightInside
    | tuple _ | keySet _ | dict _ | keyDict _ | «instance» _ _ _ | dataInstance _ _ _ _ _ =>
      simpa [HeapCalls.inplace, found, moved, object, relocateObject, relocateValue] using
        layout.binary_unsupported op (.ref address) right leftInside rightInside

theorem RuntimeLayout.binary_operation_unsupported (layout : RuntimeLayout logical physical rename)
    (op : BinOp) (left right : Value) (inPlace : Bool) (leftInside : left.edge.Within logical.length)
    (rightInside : right.edge.Within logical.length) :
    (if inPlace then HeapCalls.inplace op (relocateValue rename left) (relocateValue rename right)
      else Mutable.binary op (relocateValue rename left) (relocateValue rename right)) physical = none ↔
    (if inPlace then HeapCalls.inplace op left right else Mutable.binary op left right) logical = none := by
  cases inPlace
  · exact layout.binary_unsupported op left right leftInside rightInside
  · exact layout.inplace_unsupported op left right leftInside rightInside

end FormalSW.PyAst.Mutable.Relocation
