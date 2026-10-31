import lang.py.FormalSW.BinaryDispatchRelocation

/-! Binary operations retain existing memory even on exceptional exits. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

def HeapGrows {α : Type} (action : Eval α) : Prop :=
  ∀ heap outcome after, action heap = some (outcome, after) → heap.length ≤ after.length

theorem HeapGrows.pure (value : α) : HeapGrows (pure value : Eval α) := by
  intro heap outcome after executed
  have same : Except.ok value = outcome ∧ heap = after := by simpa using executed
  simp [← same.2]

theorem HeapGrows.throw (exception : ExceptionObject) : HeapGrows (throw exception : Eval α) := by
  intro heap outcome after executed
  have same : Except.error exception = outcome ∧ heap = after := by simpa using executed
  simp [← same.2]

theorem HeapGrows.error (name : String) : HeapGrows (Mutable.error name : Eval α) := HeapGrows.throw _

theorem HeapGrows.unsupported : HeapGrows (Mutable.unsupported : Eval α) := by
  intro heap outcome after executed
  simp [Mutable.unsupported] at executed

theorem HeapGrows.get : HeapGrows (get : Eval Heap) := by
  intro heap outcome after executed
  have same : Except.ok heap = outcome ∧ heap = after := by simpa using executed
  simp [← same.2]

theorem HeapGrows.modify (change : Heap → Heap) (grows : ∀ heap, heap.length ≤ (change heap).length) :
    HeapGrows (modify change : Eval PUnit) := by
  intro heap outcome after executed
  have same : Except.ok PUnit.unit = outcome ∧ change heap = after := by simpa using executed
  simpa [← same.2] using grows heap

theorem HeapGrows.bind {α β : Type} {action : Eval α} {next : α → Eval β}
    (first : HeapGrows action) (rest : ∀ value, HeapGrows (next value)) : HeapGrows (action >>= next) := by
  intro heap outcome after executed
  cases tested : action heap with
  | none => simp [eval_bind, tested] at executed
  | some pair =>
    rcases pair with ⟨result, middle⟩
    have larger := first heap result middle tested
    cases result with
    | error exception =>
      have same : Except.error exception = outcome ∧ middle = after := by simpa [eval_bind, tested] using executed
      simpa [← same.2] using larger
    | ok value =>
      exact Nat.le_trans larger (rest value middle outcome after (by simpa [eval_bind, tested] using executed))

theorem HeapGrows.allocate (items : List Value) : HeapGrows (Mutable.allocate items) := by
  intro heap outcome after executed
  have same : Except.ok (Value.ref heap.length) = outcome ∧ heap ++ [.list items] = after := by
    simpa [Mutable.allocate, Except.map] using executed
  simp [← same.2]

theorem HeapGrows.allocateBuffer (bytes : List UInt8) : HeapGrows (Mutable.allocateBuffer bytes) := by
  intro heap outcome after executed
  have same : Except.ok (Value.ref heap.length) = outcome ∧ heap ++ [.bytearray bytes] = after := by
    simpa [Mutable.allocateBuffer, Except.map] using executed
  simp [← same.2]

theorem HeapGrows.allocateSet (items : List Constant) : HeapGrows (Mutable.allocateSet items) := by
  intro heap outcome after executed
  have same : Except.ok (Value.ref heap.length) = outcome ∧ heap ++ [.set items] = after := by
    simpa [Mutable.allocateSet, Except.map] using executed
  simp [← same.2]

theorem HeapGrows.allocateTuple (items : List Value) : HeapGrows (Mutable.allocateTuple items) := by
  intro heap outcome after executed
  by_cases empty : items.isEmpty = true
  · cases found : heap.findIdx? (fun object => decide (object = .tuple [])) <;>
      simp [Mutable.allocateTuple, empty, found, Except.map] at executed <;>
      rcases executed with ⟨rfl, rfl⟩ <;> simp
  · simp [Mutable.allocateTuple, empty, Except.map] at executed
    rcases executed with ⟨rfl, rfl⟩
    simp

theorem HeapGrows.array (value : Value) : HeapGrows (Mutable.array value) := by
  unfold Mutable.array
  repeat' first
    | exact HeapGrows.pure _
    | exact HeapGrows.throw _
    | exact HeapGrows.unsupported
    | split
    | apply HeapGrows.bind HeapGrows.get; intro heap

theorem HeapGrows.invalidBinary (op : BinOp) (value : Value) : HeapGrows (Mutable.invalidBinary op value) := by
  unfold Mutable.invalidBinary
  repeat' first
    | exact HeapGrows.throw _
    | exact HeapGrows.unsupported
    | split
    | apply HeapGrows.bind HeapGrows.get; intro heap

theorem HeapGrows.setUnion (left right : Nat) (inPlace : Bool) : HeapGrows (Mutable.setUnion left right inPlace) := by
  unfold Mutable.setUnion
  apply HeapGrows.bind HeapGrows.get
  intro heap
  apply HeapGrows.bind HeapGrows.get
  intro otherHeap
  split
  · cases inPlace with
    | false => exact HeapGrows.allocateSet _
    | true =>
      apply HeapGrows.bind (HeapGrows.modify _ (by intro heap; simp))
      intro ignored
      exact HeapGrows.pure _
  · exact HeapGrows.unsupported

theorem HeapGrows.setDifference (left right : Nat) (inPlace : Bool) : HeapGrows (Mutable.setDifference left right inPlace) := by
  unfold Mutable.setDifference
  apply HeapGrows.bind HeapGrows.get
  intro heap
  apply HeapGrows.bind HeapGrows.get
  intro otherHeap
  split
  · cases inPlace with
    | false => exact HeapGrows.allocateSet _
    | true =>
      apply HeapGrows.bind (HeapGrows.modify _ (by intro heap; simp))
      intro ignored
      exact HeapGrows.pure _
  all_goals first | exact HeapGrows.unsupported | exact HeapGrows.throw _

theorem HeapGrows.binary_scalar_ref (op : BinOp) (left : Constant) (right : Nat) :
    HeapGrows (Mutable.binary op (.scalar left) (.ref right)) := by
  cases left <;> cases op <;> dsimp only [Mutable.binary]
  all_goals with_reducible repeat' first
    | exact HeapGrows.pure _
    | exact HeapGrows.throw _
    | exact HeapGrows.unsupported
    | exact HeapGrows.allocate _
    | exact HeapGrows.allocateTuple _
    | exact HeapGrows.allocateBuffer _
    | exact HeapGrows.setUnion _ _ _
    | exact HeapGrows.setDifference _ _ _
    | exact HeapGrows.invalidBinary _ _
    | exact HeapGrows.error _
    | split
    | apply HeapGrows.bind (HeapGrows.array _); intro items
    | apply HeapGrows.bind HeapGrows.get; intro heap

theorem HeapGrows.binary_ref_scalar (op : BinOp) (left : Nat) (right : Constant) :
    HeapGrows (Mutable.binary op (.ref left) (.scalar right)) := by
  cases right <;> cases op <;> dsimp only [Mutable.binary]
  all_goals with_reducible repeat' first
    | exact HeapGrows.pure _
    | exact HeapGrows.throw _
    | exact HeapGrows.unsupported
    | exact HeapGrows.allocate _
    | exact HeapGrows.allocateTuple _
    | exact HeapGrows.allocateBuffer _
    | exact HeapGrows.setUnion _ _ _
    | exact HeapGrows.setDifference _ _ _
    | exact HeapGrows.invalidBinary _ _
    | exact HeapGrows.error _
    | split
    | apply HeapGrows.bind (HeapGrows.array _); intro items
    | apply HeapGrows.bind HeapGrows.get; intro heap

theorem HeapGrows.binary_refs (op : BinOp) (left right : Nat) :
    HeapGrows (Mutable.binary op (.ref left) (.ref right)) := by
  cases op <;> dsimp only [Mutable.binary]
  all_goals with_reducible repeat' first
    | exact HeapGrows.pure _
    | exact HeapGrows.throw _
    | exact HeapGrows.unsupported
    | exact HeapGrows.allocate _
    | exact HeapGrows.allocateTuple _
    | exact HeapGrows.allocateBuffer _
    | exact HeapGrows.setUnion _ _ _
    | exact HeapGrows.setDifference _ _ _
    | exact HeapGrows.invalidBinary _ _
    | exact HeapGrows.error _
    | split
    | apply HeapGrows.bind (HeapGrows.array _); intro items
    | apply HeapGrows.bind HeapGrows.get; intro heap

theorem HeapGrows.binary (op : BinOp) (left right : Value) : HeapGrows (Mutable.binary op left right) := by
  cases left with
  | scalar left =>
    cases right with
    | scalar right =>
      rw [HeapCalls.Relocation.binary_scalars]
      intro heap outcome after executed
      have same := (HeapCalls.Relocation.scalarResult_effect heap after (scalarBinary op left right) outcome executed).1
      simp [same]
    | ref address => exact HeapGrows.binary_scalar_ref op left address
  | ref address =>
    cases right with
    | scalar right => exact HeapGrows.binary_ref_scalar op address right
    | ref other => exact HeapGrows.binary_refs op address other

theorem HeapGrows.sequence (value : Value) : HeapGrows (Mutable.sequence value) := by
  intro heap outcome after executed
  simp [sequence_keeps_heap heap after value outcome executed]

theorem HeapGrows.integer (value : Value) : HeapGrows (Mutable.integer value) := by
  intro heap outcome after executed
  simp [integer_keeps_heap heap after value outcome executed]

theorem HeapGrows.bufferOperand (receiver : Option Nat) (value : Value) : HeapGrows (bufferOperand receiver value) := by
  intro heap outcome after executed
  simp [bufferOperand_keeps_heap heap after receiver value outcome executed]

theorem HeapGrows.storeBufferResult (address : Nat) (bytes : List UInt8) (inPlace : Bool) :
    HeapGrows (storeBufferResult address bytes inPlace) := by
  cases inPlace with
  | false => exact HeapGrows.allocateBuffer bytes
  | true =>
    apply HeapGrows.bind (HeapGrows.modify _ (by intro heap; simp))
    intro ignored
    exact HeapGrows.pure _

theorem HeapGrows.inplaceBinary (op : BinOp) (left right : Value) : HeapGrows (Mutable.inplaceBinary op left right) := by
  unfold Mutable.inplaceBinary
  split
  · exact HeapGrows.setDifference _ _ _
  · exact HeapGrows.setUnion _ _ _
  · exact HeapGrows.binary _ _ _

theorem HeapGrows.inplace (op : BinOp) (left right : Value) : HeapGrows (HeapCalls.inplace op left right) := by
  intro heap outcome after executed
  cases left with
  | scalar scalar => exact HeapGrows.binary op (.scalar scalar) right heap outcome after executed
  | ref address =>
    cases found : heap[address]? with
    | none => simp [HeapCalls.inplace, found, Mutable.unsupported] at executed
    | some object =>
      cases object with
      | list items =>
        by_cases added : op = .add
        · subst op
          rw [HeapCalls.Relocation.inplace_add_list_eval heap address items right found] at executed
          exact (HeapGrows.bind (HeapGrows.sequence right) (fun more =>
            HeapGrows.bind (HeapGrows.modify _ (by intro heap; simp)) (fun _ => HeapGrows.pure _))) heap outcome after executed
        · by_cases multiplied : op = .mult
          · subst op
            rw [HeapCalls.Relocation.inplace_mult_list_value_eval heap address items right found] at executed
            exact (HeapGrows.bind (HeapGrows.integer right) (fun count =>
              HeapGrows.bind (HeapGrows.modify _ (by intro heap; simp)) (fun _ => HeapGrows.pure _))) heap outcome after executed
          · rw [inplace_list_fallback heap address items op right found added multiplied] at executed
            exact HeapGrows.binary op (.ref address) right heap outcome after executed
      | bytearray bytes =>
        by_cases added : op = .add
        · subst op
          rw [inplace_add_buffer_eval heap address bytes right found] at executed
          exact (HeapGrows.bind (HeapGrows.bufferOperand (some address) right)
            (fun more => HeapGrows.storeBufferResult address (bytes ++ more) true)) heap outcome after executed
        · by_cases multiplied : op = .mult
          · subst op
            rw [inplace_mult_buffer_eval heap address bytes right found] at executed
            exact (HeapGrows.bind (HeapGrows.integer right)
              (fun count => HeapGrows.storeBufferResult address (List.replicate count.toNat bytes).flatten true)) heap outcome after executed
          · rw [inplace_buffer_fallback heap address bytes op right found added multiplied] at executed
            exact HeapGrows.binary op (.ref address) right heap outcome after executed
      | set items =>
        exact HeapGrows.inplaceBinary op (.ref address) right heap outcome after
          (by simpa [HeapCalls.inplace, found] using executed)
      | _ =>
        exact HeapGrows.binary op (.ref address) right heap outcome after
          (by simpa [HeapCalls.inplace, found] using executed)

theorem HeapGrows.binary_operation (op : BinOp) (left right : Value) (inPlace : Bool) :
    HeapGrows (if inPlace then HeapCalls.inplace op left right else Mutable.binary op left right) := by
  cases inPlace
  · exact HeapGrows.binary op left right
  · exact HeapGrows.inplace op left right

end FormalSW.PyAst.Mutable.Relocation
