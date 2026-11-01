import lang.py.FormalSW.BufferArithmeticRelocation
import lang.py.FormalSW.ArithmeticRelocation
import lang.py.FormalSW.SetOperationsRelocation

/-! Ordinary and augmented binary evaluation preserve complete outcomes across runtime object layouts. -/
namespace FormalSW.PyAst.Mutable.Relocation
open HeapCalls.Relocation
set_option Elab.async false

variable {logical physical : Heap} {rename : Nat → Nat}

theorem ExecutionLayout.scalar_result (layout : ExecutionLayout logical physical rename)
    (result : Option (Except ExceptionObject Constant)) :
    EvalRelocates logical physical rename (HeapCalls.scalarResult result) (HeapCalls.scalarResult result) := by
  intro outcome after executed
  obtain ⟨same, scalar⟩ := scalarResult_effect logical after result outcome executed
  subst after
  refine ⟨physical, rename, ?_, layout, fun _ _ => rfl, Nat.le_refl _, ?_⟩
  · simpa only [executed, Option.map_some] using scalarResult_relocates logical physical rename result
  · intro value success
    obtain ⟨constant, rfl⟩ := scalar value success
    trivial

theorem ExecutionLayout.invalid_binary (layout : ExecutionLayout logical physical rename)
    (op : BinOp) (left : Value) (inside : left.edge.Within logical.length) :
    EvalRelocates logical physical rename (Mutable.invalidBinary op left)
      (Mutable.invalidBinary op (relocateValue rename left)) := by
  by_cases subtraction : (op == .sub) = true
  · cases left with
    | scalar scalar =>
      apply (layout.throw_relocates {typeName := "TypeError", args := []}).congr <;>
        simp [Mutable.invalidBinary, subtraction, relocateValue, error]
    | ref address =>
      have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
      have moved := layout.runtime.lookup address _ found
      apply (layout.throw_relocates {typeName := "TypeError", args := []}).congr <;>
        simp [Mutable.invalidBinary, subtraction, found, moved, relocateValue, error]
  · by_cases modulo : (op == .mod) = true
    · cases left with
      | scalar scalar =>
        cases scalar with
        | bytes =>
          apply (unsupported_relocates logical physical rename).congr <;>
            simp [Mutable.invalidBinary, subtraction, modulo, relocateValue]
        | int | bool | string | none =>
          apply (layout.throw_relocates {typeName := "TypeError", args := []}).congr <;>
            simp [Mutable.invalidBinary, subtraction, modulo, relocateValue, error]
      | ref address =>
        have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
        have moved := layout.runtime.lookup address _ found
        cases object : logical[address] with
        | bytearray =>
          apply (unsupported_relocates logical physical rename).congr <;>
            simp [Mutable.invalidBinary, subtraction, modulo, found, moved, object, relocateObject, relocateValue]
        | list _ | tuple _ | set _ | keySet _ | dict _ | keyDict _ | «instance» _ _ _ | dataInstance _ _ _ _ _ =>
          apply (layout.throw_relocates {typeName := "TypeError", args := []}).congr <;>
            simp [Mutable.invalidBinary, subtraction, modulo, found, moved, object, relocateObject, relocateValue, error]
    · apply (layout.throw_relocates {typeName := "TypeError", args := []}).congr <;>
        simp [Mutable.invalidBinary, subtraction, modulo, error]

/-- Boolean repetition uses the same conversion as signed integer repetition. -/
theorem binary_mult_convert (heap : Heap) (address : Nat) (right : Value) :
    Mutable.binary .mult (.ref address) right heap =
      (Mutable.integer right >>= fun count => Mutable.binary .mult (.ref address) (.scalar (.int count))) heap := by
  cases right with
  | ref other => rfl
  | scalar scalar =>
    cases scalar with
    | bool keep => cases keep <;> rfl
    | int | string | bytes | none => rfl

theorem ExecutionLayout.binary_mult_ref_int (layout : ExecutionLayout logical physical rename)
    (address : Nat) (count : Int) (inside : address < logical.length) :
    EvalRelocates logical physical rename (Mutable.binary .mult (.ref address) (.scalar (.int count)))
      (Mutable.binary .mult (.ref (rename address)) (.scalar (.int count))) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
  have moved := layout.runtime.lookup address _ found
  cases object : logical[address] with
  | list items => exact layout.binary_mult_list address items count (by simpa only [object] using found)
  | tuple items => exact layout.binary_mult_tuple address items count (by simpa only [object] using found)
  | bytearray bytes => exact layout.mult_buffer address bytes (.scalar (.int count)) false (by simpa only [object] using found)
  | set _ | keySet _ | dict _ | keyDict _ | «instance» _ _ _ | dataInstance _ _ _ _ _ =>
    apply (layout.throw_relocates {typeName := "TypeError", args := []}).congr <;>
      simp [Mutable.binary, show (BinOp.mult == BinOp.mult) = true from rfl, found, moved, object, relocateObject, error]

theorem ExecutionLayout.binary_mult_ref (layout : ExecutionLayout logical physical rename)
    (address : Nat) (right : Value) (inside : address < logical.length) :
    EvalRelocates logical physical rename (Mutable.binary .mult (.ref address) right)
      (Mutable.binary .mult (.ref (rename address)) (relocateValue rename right)) := by
  have converted := EvalRelocates.readonly_bind layout (Mutable.integer right) (Mutable.integer (relocateValue rename right))
    (fun count => Mutable.binary .mult (.ref address) (.scalar (.int count)))
    (fun count => Mutable.binary .mult (.ref (rename address)) (.scalar (.int count)))
    (integer_relocates logical physical rename right) (fun outcome after => integer_keeps_heap logical after right outcome)
    (fun count _ => layout.binary_mult_ref_int address count inside)
  exact converted.congr (binary_mult_convert logical address right)
    (binary_mult_convert physical (rename address) (relocateValue rename right))

/-- Matching sequence kinds delegate to their allocating and tuple-reuse rules; mismatches raise. -/
theorem ExecutionLayout.binary_add_refs (layout : ExecutionLayout logical physical rename)
    (left right : Nat) (leftObject rightObject : Object)
    (first : logical[left]? = some leftObject) (second : logical[right]? = some rightObject) :
    EvalRelocates logical physical rename (Mutable.binary .add (.ref left) (.ref right))
      (Mutable.binary .add (.ref (rename left)) (.ref (rename right))) := by
  have movedLeft := layout.runtime.lookup left _ first
  have movedRight := layout.runtime.lookup right _ second
  cases leftObject with
  | bytearray bytes => exact layout.add_buffer left bytes (.ref right) false first (List.getElem?_eq_some_iff.mp second).1
  | list items =>
    cases rightObject <;> first
      | exact layout.binary_add_lists left right items _ first second
      | apply (layout.throw_relocates {typeName := "TypeError", args := []}).congr <;>
          simp [Mutable.binary, show (BinOp.add == BinOp.add) = true from rfl, first, second,
            movedLeft, movedRight, relocateObject, error]
  | tuple items =>
    cases rightObject <;> first
      | exact layout.binary_add_tuples left right items _ first second
      | apply (layout.throw_relocates {typeName := "TypeError", args := []}).congr <;>
          simp [Mutable.binary, show (BinOp.add == BinOp.add) = true from rfl, first, second,
            movedLeft, movedRight, relocateObject, error]
  | set _ | keySet _ | dict _ | keyDict _ | «instance» _ _ _ | dataInstance _ _ _ _ _ =>
    apply (layout.throw_relocates {typeName := "TypeError", args := []}).congr <;>
        simp [Mutable.binary, show (BinOp.add == BinOp.add) = true from rfl, first, second,
          movedLeft, movedRight, relocateObject, error]

theorem ExecutionLayout.binary_add_ref_bytes (layout : ExecutionLayout logical physical rename)
    (address : Nat) (bytes : List UInt8) (inside : address < logical.length) :
    EvalRelocates logical physical rename (Mutable.binary .add (.ref address) (.scalar (.bytes bytes)))
      (Mutable.binary .add (.ref (rename address)) (.scalar (.bytes bytes))) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
  have moved := layout.runtime.lookup address _ found
  cases object : logical[address] with
  | bytearray before => exact layout.add_buffer address before (.scalar (.bytes bytes)) false (by simpa only [object] using found) (by trivial)
  | list _ | tuple _ | set _ | keySet _ | dict _ | keyDict _ | «instance» _ _ _ | dataInstance _ _ _ _ _ =>
    apply (layout.throw_relocates {typeName := "TypeError", args := []}).congr <;>
      simp [Mutable.binary, show (BinOp.add == BinOp.add) = true from rfl, found, moved, object, relocateObject, error]

theorem ExecutionLayout.binary_add_bytes_ref (layout : ExecutionLayout logical physical rename)
    (address : Nat) (bytes : List UInt8) (inside : address < logical.length) :
    EvalRelocates logical physical rename (Mutable.binary .add (.scalar (.bytes bytes)) (.ref address))
      (Mutable.binary .add (.scalar (.bytes bytes)) (.ref (rename address))) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
  have moved := layout.runtime.lookup address _ found
  cases object : logical[address] with
  | bytearray after => exact layout.add_bytes_buffer address bytes after (by simpa only [object] using found)
  | list _ | tuple _ | set _ | keySet _ | dict _ | keyDict _ | «instance» _ _ _ | dataInstance _ _ _ _ _ =>
    apply (layout.throw_relocates {typeName := "TypeError", args := []}).congr <;>
      simp [Mutable.binary, show (BinOp.add == BinOp.add) = true from rfl, found, moved, object, relocateObject, error]

theorem ExecutionLayout.binary_refs (layout : ExecutionLayout logical physical rename)
    (op : BinOp) (left right : Nat) (leftInside : left < logical.length) (rightInside : right < logical.length) :
    EvalRelocates logical physical rename (Mutable.binary op (.ref left) (.ref right))
      (Mutable.binary op (.ref (rename left)) (.ref (rename right))) := by
  cases op with
  | add =>
    exact layout.binary_add_refs left right logical[left] logical[right]
      (List.getElem?_eq_getElem leftInside) (List.getElem?_eq_getElem rightInside)
  | sub => exact layout.setDifference left right false leftInside rightInside
  | bitOr => exact layout.setUnion left right false leftInside rightInside
  | mult => apply (layout.invalid_binary .mult (.ref left) leftInside).congr <;> rfl
  | pow => apply (layout.invalid_binary .pow (.ref left) leftInside).congr <;> rfl
  | floorDiv => apply (layout.invalid_binary .floorDiv (.ref left) leftInside).congr <;> rfl
  | mod => apply (layout.invalid_binary .mod (.ref left) leftInside).congr <;> rfl
  | bitAnd | bitXor | leftShift | rightShift =>
    exact unsupported_relocates logical physical rename

theorem ExecutionLayout.binary_ref_scalar (layout : ExecutionLayout logical physical rename)
    (op : BinOp) (address : Nat) (scalar : Constant) (inside : address < logical.length) :
    EvalRelocates logical physical rename (Mutable.binary op (.ref address) (.scalar scalar))
      (Mutable.binary op (.ref (rename address)) (.scalar scalar)) := by
  cases op with
  | mult => exact layout.binary_mult_ref address (.scalar scalar) inside
  | add =>
    cases scalar with
    | bytes bytes => exact layout.binary_add_ref_bytes address bytes inside
    | int | bool | string | none =>
      apply (layout.throw_relocates {typeName := "TypeError", args := []}).congr <;> rfl
  | sub => apply (layout.invalid_binary .sub (.ref address) inside).congr <;> cases scalar <;> rfl
  | pow => apply (layout.invalid_binary .pow (.ref address) inside).congr <;> cases scalar <;> rfl
  | floorDiv => apply (layout.invalid_binary .floorDiv (.ref address) inside).congr <;> cases scalar <;> rfl
  | mod => apply (layout.invalid_binary .mod (.ref address) inside).congr <;> cases scalar <;> rfl
  | bitAnd | bitOr | bitXor | leftShift | rightShift =>
    exact unsupported_relocates logical physical rename

theorem ExecutionLayout.binary_scalar_ref (layout : ExecutionLayout logical physical rename)
    (op : BinOp) (scalar : Constant) (address : Nat) (inside : address < logical.length) :
    EvalRelocates logical physical rename (Mutable.binary op (.scalar scalar) (.ref address))
      (Mutable.binary op (.scalar scalar) (.ref (rename address))) := by
  cases op with
  | mult =>
    exact (layout.binary_mult_ref address (.scalar scalar) inside).congr
      (binary_mult_ref_value_comm logical address (.scalar scalar))
      (binary_mult_ref_value_comm physical (rename address) (.scalar scalar))
  | add =>
    cases scalar with
    | bytes bytes => exact layout.binary_add_bytes_ref address bytes inside
    | int | bool | string | none =>
      apply (layout.throw_relocates {typeName := "TypeError", args := []}).congr <;> rfl
  | sub | pow | floorDiv =>
    apply (layout.throw_relocates {typeName := "TypeError", args := []}).congr <;> cases scalar <;> rfl
  | mod =>
    cases scalar with
    | bytes | string => exact unsupported_relocates logical physical rename
    | int | bool | none =>
      apply (layout.throw_relocates {typeName := "TypeError", args := []}).congr <;> rfl
  | bitAnd | bitOr | bitXor | leftShift | rightShift =>
    exact unsupported_relocates logical physical rename

/-- Every completed ordinary binary operation derives its counterpart, including allocation and exceptions.
The statement covers the interpreter's supported behavior, not custom Python operator protocols. -/
theorem ExecutionLayout.binary (layout : ExecutionLayout logical physical rename)
    (op : BinOp) (left right : Value) (leftInside : left.edge.Within logical.length)
    (rightInside : right.edge.Within logical.length) :
    EvalRelocates logical physical rename (Mutable.binary op left right)
      (Mutable.binary op (relocateValue rename left) (relocateValue rename right)) := by
  cases left with
  | scalar left =>
    cases right with
    | scalar right =>
      simpa only [binary_scalars, relocateValue] using layout.scalar_result (scalarBinary op left right)
    | ref right => exact layout.binary_scalar_ref op left right rightInside
  | ref left =>
    cases right with
    | scalar right => exact layout.binary_ref_scalar op left right leftInside
    | ref right => exact layout.binary_refs op left right leftInside rightInside

theorem ExecutionLayout.inplace_binary (layout : ExecutionLayout logical physical rename)
    (op : BinOp) (left right : Value) (leftInside : left.edge.Within logical.length)
    (rightInside : right.edge.Within logical.length) :
    EvalRelocates logical physical rename (Mutable.inplaceBinary op left right)
      (Mutable.inplaceBinary op (relocateValue rename left) (relocateValue rename right)) := by
  cases op with
  | sub =>
    cases left <;> cases right <;> first
      | exact layout.setDifference _ _ true leftInside rightInside
      | exact layout.binary .sub _ _ leftInside rightInside
  | bitOr =>
    cases left <;> cases right <;> first
      | exact layout.setUnion _ _ true leftInside rightInside
      | exact layout.binary .bitOr _ _ leftInside rightInside
  | add => exact layout.binary .add left right leftInside rightInside
  | mult => exact layout.binary .mult left right leftInside rightInside
  | bitAnd => exact layout.binary .bitAnd left right leftInside rightInside
  | bitXor => exact layout.binary .bitXor left right leftInside rightInside
  | leftShift => exact layout.binary .leftShift left right leftInside rightInside
  | rightShift => exact layout.binary .rightShift left right leftInside rightInside
  | pow => exact layout.binary .pow left right leftInside rightInside
  | floorDiv => exact layout.binary .floorDiv left right leftInside rightInside
  | mod => exact layout.binary .mod left right leftInside rightInside

/-- List operations other than extension and repetition use ordinary binary dispatch. -/
theorem inplace_list_fallback (heap : Heap) (address : Nat) (items : List Value) (op : BinOp) (right : Value)
    (found : heap[address]? = some (.list items)) (notAdd : op ≠ .add) (notMult : op ≠ .mult) :
    HeapCalls.inplace op (.ref address) right heap = Mutable.binary op (.ref address) right heap := by
  simp [HeapCalls.inplace, found]
  cases op <;> try contradiction
  all_goals cases right with
    | ref other => rfl
    | scalar scalar => cases scalar <;> rfl

theorem inplace_buffer_fallback (heap : Heap) (address : Nat) (bytes : List UInt8) (op : BinOp) (right : Value)
    (found : heap[address]? = some (.bytearray bytes)) (notAdd : op ≠ .add) (notMult : op ≠ .mult) :
    HeapCalls.inplace op (.ref address) right heap = Mutable.binary op (.ref address) right heap := by
  cases op <;> simp_all [HeapCalls.inplace]

/-- Augmented dispatch retains the actual mutating rules and ordinary fallback operations. -/
theorem ExecutionLayout.inplace (layout : ExecutionLayout logical physical rename)
    (op : BinOp) (left right : Value) (leftInside : left.edge.Within logical.length)
    (rightInside : right.edge.Within logical.length) :
    EvalRelocates logical physical rename (HeapCalls.inplace op left right)
      (HeapCalls.inplace op (relocateValue rename left) (relocateValue rename right)) := by
  cases left with
  | scalar scalar => exact layout.binary op (.scalar scalar) right leftInside rightInside
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem leftInside
    have moved := layout.runtime.lookup address _ found
    cases object : logical[address] with
    | list items =>
      have first : logical[address]? = some (.list items) := by simpa only [object] using found
      have second : physical[rename address]? = some (.list (items.map (relocateValue rename))) :=
        layout.runtime.lookup _ _ first
      by_cases added : op = .add
      · subst op
        exact layout.inplace_add_list address items right first rightInside
      · by_cases multiplied : op = .mult
        · subst op
          exact layout.inplace_mult_list_value address items right first
        · exact (layout.binary op (.ref address) right leftInside rightInside).congr
            (inplace_list_fallback logical address items op right first added multiplied)
            (inplace_list_fallback physical (rename address) _ op (relocateValue rename right) second added multiplied)
    | bytearray bytes =>
      have first : logical[address]? = some (.bytearray bytes) := by simpa only [object] using found
      have second : physical[rename address]? = some (.bytearray bytes) := layout.runtime.lookup _ _ first
      by_cases added : op = .add
      · subst op
        exact layout.add_buffer address bytes right true first rightInside
      · by_cases multiplied : op = .mult
        · subst op
          exact layout.mult_buffer address bytes right true first
        · exact (layout.binary op (.ref address) right leftInside rightInside).congr
            (inplace_buffer_fallback logical address bytes op right first added multiplied)
            (inplace_buffer_fallback physical (rename address) bytes op (relocateValue rename right) second added multiplied)
    | set items =>
      apply (layout.inplace_binary op (.ref address) right leftInside rightInside).congr <;>
        simp [HeapCalls.inplace, found, moved, object, relocateObject, relocateValue]
    | tuple _ | keySet _ | dict _ | keyDict _ | «instance» _ _ _ | dataInstance _ _ _ _ _ =>
      apply (layout.binary op (.ref address) right leftInside rightInside).congr <;>
        simp [HeapCalls.inplace, found, moved, object, relocateObject, relocateValue]

theorem ExecutionLayout.binary_operation (layout : ExecutionLayout logical physical rename)
    (op : BinOp) (left right : Value) (inPlace : Bool) (leftInside : left.edge.Within logical.length)
    (rightInside : right.edge.Within logical.length) :
    EvalRelocates logical physical rename
      (if inPlace then HeapCalls.inplace op left right else Mutable.binary op left right)
      (if inPlace then HeapCalls.inplace op (relocateValue rename left) (relocateValue rename right)
        else Mutable.binary op (relocateValue rename left) (relocateValue rename right)) := by
  cases inPlace
  · exact layout.binary op left right leftInside rightInside
  · exact layout.inplace op left right leftInside rightInside

end FormalSW.PyAst.Mutable.Relocation

namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- A completed binary machine step derives the other step for every modeled operator and operand kind. -/
theorem step_binary_operation_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (op : BinOp) (left right : Value) (inPlace : Bool) (stack : List Frame) (globals : Mutable.Globals)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) (outcome : Except ExceptionObject Value) (after : Mutable.Heap)
    (executed : (if inPlace then inplace op left right else Mutable.binary op left right) logical = some (outcome, after)) :
    ∃ other nextMap, ExecutionLayout after other nextMap ∧
      (∀ address < logical.length, nextMap address = rename address) ∧
      GlobalsWithin after.length globals ∧
      relocateGlobals nextMap globals = relocateGlobals rename globals ∧
      step module physicalAnchors
          (relocateState rename physical ⟨.value right, .binaryRight op left inPlace :: stack, logical⟩)
          (relocateGlobals rename globals) =
        relocateStep nextMap other physicalAnchors
          (step module logicalAnchors ⟨.value right, .binaryRight op left inPlace :: stack, logical⟩ globals) ∧
      StepWithin (step module logicalAnchors ⟨.value right, .binaryRight op left inPlace :: stack, logical⟩ globals) :=
  step_binary_relocates module logical physical rename logicalAnchors physicalAnchors op left right inPlace stack globals
    leftInside stackInside globalsInside (layout.binary_operation op left right inPlace leftInside rightInside) outcome after executed

end FormalSW.PyAst.HeapCalls.Relocation
