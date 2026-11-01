import lang.py.FormalSW.ListInplaceRelocation

/-! Buffer arithmetic retains allocation, aliases, and self-extension errors across layouts. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

/-- The operand read shared by ordinary and augmented buffer addition.
A captured receiver rejects nonempty self-extension before any write. -/
def bufferOperand (receiver : Option Nat) (right : Value) : Eval (List UInt8) :=
  match right with
  | .scalar (.bytes bytes) => pure bytes
  | .ref other => do
    match (← get)[other]? with
    | some (.bytearray bytes) =>
      if receiver = some other ∧ !bytes.isEmpty then error "BufferError" else pure bytes
    | none => unsupported
    | some _ => error "TypeError"
  | _ => error "TypeError"

/-- The shared storage branch is equated to the actual operators below. -/
def storeBufferResult (address : Nat) (bytes : List UInt8) (inPlace : Bool) : Eval Value := do
  if inPlace then
    modify fun heap => heap.set address (.bytearray bytes)
    return .ref address
  else Mutable.allocateBuffer bytes

theorem binary_add_buffer_eval (heap : Heap) (address : Nat) (bytes : List UInt8) (right : Value)
    (found : heap[address]? = some (.bytearray bytes)) :
    Mutable.binary .add (.ref address) right heap =
      (bufferOperand none right >>= fun more => storeBufferResult address (bytes ++ more) false) heap := by
  cases right with
  | ref other =>
    cases otherFound : heap[other]? with
    | none => simp [Mutable.binary, bufferOperand, found, otherFound, unsupported, show (BinOp.add == BinOp.add) = true from rfl]
    | some object =>
      cases object <;> simp [Mutable.binary, bufferOperand, storeBufferResult, found, otherFound,
        show (BinOp.add == BinOp.add) = true from rfl, error, eval_bind]
  | scalar scalar =>
    cases scalar <;> simp [Mutable.binary, bufferOperand, storeBufferResult, found,
      show (BinOp.add == BinOp.add) = true from rfl, show (BinOp.add == BinOp.mult) = false from rfl,
      Mutable.invalidBinary, show (BinOp.add == BinOp.sub) = false from rfl,
      show (BinOp.add == BinOp.mod) = false from rfl, error, eval_bind]
    all_goals split <;> rfl

theorem inplace_add_buffer_eval (heap : Heap) (address : Nat) (bytes : List UInt8) (right : Value)
    (found : heap[address]? = some (.bytearray bytes)) :
    HeapCalls.inplace .add (.ref address) right heap =
      (bufferOperand (some address) right >>= fun more => storeBufferResult address (bytes ++ more) true) heap := by
  cases right with
  | ref other =>
    cases otherFound : heap[other]? with
    | none => simp [HeapCalls.inplace, bufferOperand, found, otherFound, unsupported]
    | some object =>
      cases object <;> simp [HeapCalls.inplace, bufferOperand, storeBufferResult, found, otherFound,
        show address = other ↔ other = address from eq_comm, error, eval_bind, Except.map]
      split <;> rfl
  | scalar scalar =>
    cases scalar <;> simp [HeapCalls.inplace, bufferOperand, storeBufferResult, found, error, eval_bind, Except.map]

theorem binary_mult_buffer_eval (heap : Heap) (address : Nat) (bytes : List UInt8) (right : Value)
    (found : heap[address]? = some (.bytearray bytes)) :
    Mutable.binary .mult (.ref address) right heap =
      (Mutable.integer right >>= fun count => storeBufferResult address (List.replicate count.toNat bytes).flatten false) heap := by
  cases right with
  | ref other =>
    simp [Mutable.binary, Mutable.integer, show (BinOp.mult == BinOp.add) = false from rfl,
      show (BinOp.mult == BinOp.sub) = false from rfl, show (BinOp.mult == BinOp.mod) = false from rfl,
      Mutable.invalidBinary, error, eval_bind]
  | scalar scalar =>
    cases scalar <;> simp [Mutable.binary, Mutable.integer, storeBufferResult, found,
      show (BinOp.mult == BinOp.mult) = true from rfl, show (BinOp.mult == BinOp.add) = false from rfl,
      Mutable.invalidBinary, show (BinOp.mult == BinOp.sub) = false from rfl,
      show (BinOp.mult == BinOp.mod) = false from rfl, error, eval_bind]
    all_goals split <;> rfl

theorem inplace_mult_buffer_eval (heap : Heap) (address : Nat) (bytes : List UInt8) (right : Value)
    (found : heap[address]? = some (.bytearray bytes)) :
    HeapCalls.inplace .mult (.ref address) right heap =
      (Mutable.integer right >>= fun count => storeBufferResult address (List.replicate count.toNat bytes).flatten true) heap := by
  simp [HeapCalls.inplace, storeBufferResult, found]

theorem binary_mult_ref_value_comm (heap : Heap) (address : Nat) (value : Value) :
    Mutable.binary .mult value (.ref address) heap = Mutable.binary .mult (.ref address) value heap := by
  cases value with
  | ref other => rfl
  | scalar scalar => cases scalar <;> rfl

/-- Bytes on the left produce an immutable value, rather than a new bytearray. -/
theorem binary_add_bytes_buffer_eval (heap : Heap) (address : Nat) (left right : List UInt8)
    (found : heap[address]? = some (.bytearray right)) :
    Mutable.binary .add (.scalar (.bytes left)) (.ref address) heap =
      some (.ok (.scalar (.bytes (left ++ right))), heap) := by
  simp [Mutable.binary, found, show (BinOp.add == BinOp.add) = true from rfl]

variable {logical physical : Heap} {rename : Nat → Nat}

theorem RuntimeLayout.bufferOperand (layout : RuntimeLayout logical physical rename) (receiver : Option Nat) (right : Value)
    (receiverInside : ∀ address, receiver = some address → address < logical.length)
    (rightInside : right.edge.Within logical.length) :
    bufferOperand (receiver.map rename) (relocateValue rename right) physical =
      (bufferOperand receiver right logical).map (fun result => (result.1, physical)) := by
  cases right with
  | scalar scalar => cases scalar <;> simp [Relocation.bufferOperand, relocateValue, error]
  | ref other =>
    have same : receiver.map rename = some (rename other) ↔ receiver = some other := by
      cases receiver with
      | none => simp
      | some address =>
        simp only [Option.map_some, Option.some.injEq]
        exact ⟨layout.injective address (receiverInside address rfl) other rightInside, congrArg rename⟩
    have found : logical[other]? = some logical[other] := List.getElem?_eq_getElem rightInside
    have moved := layout.lookup other _ found
    cases object : logical[other] <;>
      simp [Relocation.bufferOperand, relocateValue, found, object, moved, relocateObject, same, error]
    split <;> rfl

theorem bufferOperand_keeps_heap (heap after : Heap) (receiver : Option Nat) (right : Value)
    (outcome : Except ExceptionObject (List UInt8))
    (executed : bufferOperand receiver right heap = some (outcome, after)) : after = heap := by
  cases right with
  | scalar scalar =>
    cases scalar <;> simp [bufferOperand, error] at executed
    all_goals exact executed.2.symm
  | ref other =>
    cases found : heap[other]? with
    | none => simp [bufferOperand, found, unsupported] at executed
    | some object =>
      cases object <;> simp [bufferOperand, found, error] at executed
      all_goals first
        | exact executed.2.symm
        | (split at executed <;> simp at executed <;> exact executed.2.symm)

theorem ExecutionLayout.storeBufferResult (layout : ExecutionLayout logical physical rename)
    (address : Nat) (before bytes : List UInt8) (inPlace : Bool) (found : logical[address]? = some (.bytearray before)) :
    EvalRelocates logical physical rename (storeBufferResult address bytes inPlace)
      (storeBufferResult (rename address) bytes inPlace) := by
  cases inPlace with
  | false => exact layout.allocateBuffer_relocates bytes
  | true =>
    intro outcome after executed
    have same : Except.ok (.ref address) = outcome ∧ logical.set address (.bytearray bytes) = after := by
      simpa [Relocation.storeBufferResult, Except.map] using executed
    obtain ⟨rfl, rfl⟩ := same
    refine ⟨physical.set (rename address) (.bytearray bytes), rename, ?_,
      layout.set_nonempty address (.bytearray before) (.bytearray bytes) found (by simp) (by simp)
        (by simp [ObjectWithin, objectValues]), fun _ _ => rfl, by simp, ?_⟩
    · simp [Relocation.storeBufferResult, relocateValue, Except.map]
    · intro returned equal
      cases equal
      simpa only [Value.edge, Graph.Edge.Within, List.length_set] using (List.getElem?_eq_some_iff.mp found).1

/-- Both allocating and augmented addition retain operand identity tests and conversion failures. -/
theorem ExecutionLayout.add_buffer (layout : ExecutionLayout logical physical rename)
    (address : Nat) (bytes : List UInt8) (right : Value) (inPlace : Bool)
    (found : logical[address]? = some (.bytearray bytes)) (rightInside : right.edge.Within logical.length) :
    EvalRelocates logical physical rename
      (if inPlace then HeapCalls.inplace .add (.ref address) right else Mutable.binary .add (.ref address) right)
      (if inPlace then HeapCalls.inplace .add (.ref (rename address)) (relocateValue rename right)
        else Mutable.binary .add (.ref (rename address)) (relocateValue rename right)) := by
  let receiver := if inPlace then some address else none
  have bounded : ∀ selected, receiver = some selected → selected < logical.length := by
    intro selected equal
    cases inPlace <;> simp [receiver] at equal
    subst selected
    exact (List.getElem?_eq_some_iff.mp found).1
  have reads := layout.runtime.bufferOperand receiver right bounded rightInside
  have related := EvalRelocates.readonly_bind layout (bufferOperand receiver right)
    (bufferOperand (receiver.map rename) (relocateValue rename right))
    (fun more => Relocation.storeBufferResult address (bytes ++ more) inPlace)
    (fun more => Relocation.storeBufferResult (rename address) (bytes ++ more) inPlace) reads
    (fun outcome after => bufferOperand_keeps_heap logical after receiver right outcome)
    (fun _ _ => layout.storeBufferResult address bytes _ inPlace found)
  apply related.congr
  · cases inPlace <;> simp only [Bool.false_eq_true, if_false, if_true, receiver]
    · exact binary_add_buffer_eval logical address bytes right found
    · exact inplace_add_buffer_eval logical address bytes right found
  · cases inPlace <;> simp only [Bool.false_eq_true, if_false, if_true, receiver, Option.map_none, Option.map_some]
    · exact binary_add_buffer_eval physical (rename address) bytes _ (layout.runtime.lookup _ _ found)
    · exact inplace_add_buffer_eval physical (rename address) bytes _ (layout.runtime.lookup _ _ found)

/-- Counts use the existing unbounded integer model, including Boolean conversion and TypeError. -/
theorem ExecutionLayout.mult_buffer (layout : ExecutionLayout logical physical rename)
    (address : Nat) (bytes : List UInt8) (right : Value) (inPlace : Bool)
    (found : logical[address]? = some (.bytearray bytes)) :
    EvalRelocates logical physical rename
      (if inPlace then HeapCalls.inplace .mult (.ref address) right else Mutable.binary .mult (.ref address) right)
      (if inPlace then HeapCalls.inplace .mult (.ref (rename address)) (relocateValue rename right)
        else Mutable.binary .mult (.ref (rename address)) (relocateValue rename right)) := by
  have related := EvalRelocates.readonly_bind layout (Mutable.integer right) (Mutable.integer (relocateValue rename right))
    (fun count => Relocation.storeBufferResult address (List.replicate count.toNat bytes).flatten inPlace)
    (fun count => Relocation.storeBufferResult (rename address) (List.replicate count.toNat bytes).flatten inPlace)
    (integer_relocates logical physical rename right) (fun outcome after => integer_keeps_heap logical after right outcome)
    (fun _ _ => layout.storeBufferResult address bytes _ inPlace found)
  apply related.congr
  · cases inPlace
    · exact binary_mult_buffer_eval logical address bytes right found
    · exact inplace_mult_buffer_eval logical address bytes right found
  · cases inPlace
    · exact binary_mult_buffer_eval physical (rename address) bytes _ (layout.runtime.lookup _ _ found)
    · exact inplace_mult_buffer_eval physical (rename address) bytes _ (layout.runtime.lookup _ _ found)

theorem ExecutionLayout.add_bytes_buffer (layout : ExecutionLayout logical physical rename)
    (address : Nat) (left right : List UInt8) (found : logical[address]? = some (.bytearray right)) :
    EvalRelocates logical physical rename (Mutable.binary .add (.scalar (.bytes left)) (.ref address))
      (Mutable.binary .add (.scalar (.bytes left)) (.ref (rename address))) := by
  apply (layout.pure_relocates (.scalar (.bytes (left ++ right))) (by trivial)).congr
  · exact binary_add_bytes_buffer_eval logical address left right found
  · exact binary_add_bytes_buffer_eval physical (rename address) left right (layout.runtime.lookup _ _ found)

theorem ExecutionLayout.mult_buffer_left (layout : ExecutionLayout logical physical rename)
    (address : Nat) (bytes : List UInt8) (left : Value) (found : logical[address]? = some (.bytearray bytes)) :
    EvalRelocates logical physical rename (Mutable.binary .mult left (.ref address))
      (Mutable.binary .mult (relocateValue rename left) (.ref (rename address))) :=
  (layout.mult_buffer address bytes left false found).congr
    (binary_mult_ref_value_comm logical address left) (binary_mult_ref_value_comm physical (rename address) (relocateValue rename left))

end FormalSW.PyAst.Mutable.Relocation
