import lang.py.FormalSW.ItemRelocation
import lang.py.FormalSW.ListInplaceRelocation

/-! Indexed updates retain caller aliases, object bounds, and failed-write outcomes. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

theorem integer_total (heap : Heap) (value : Value) :
    ∃ outcome, Mutable.integer value heap = some (outcome, heap) := by
  cases value with
  | ref address => exact ⟨_, rfl⟩
  | scalar scalar => cases scalar <;> exact ⟨_, rfl⟩

theorem byte_total (heap : Heap) (value : Value) :
    ∃ outcome, Mutable.byte value heap = some (outcome, heap) := by
  obtain ⟨outcome, converted⟩ := integer_total heap value
  cases outcome with
  | error exception => exact ⟨.error exception, by simp [Mutable.byte, converted, eval_bind]⟩
  | ok number =>
    by_cases valid : 0 ≤ number ∧ number < 256
    · exact ⟨.ok (UInt8.ofNat number.toNat), by simp [Mutable.byte, converted, eval_bind, valid]⟩
    · exact ⟨.error ⟨"ValueError", []⟩, by simp [Mutable.byte, converted, eval_bind, valid, error]⟩

theorem byte_relocates (logical physical : Heap) (rename : Nat → Nat) (value : Value) :
    Mutable.byte (relocateValue rename value) physical =
      (Mutable.byte value logical).map (fun result => (result.1, physical)) := by
  have paired := integer_relocates logical physical rename value
  obtain ⟨outcome, converted⟩ := integer_total logical value
  cases outcome with
  | error exception => simp [Mutable.byte, paired, converted, eval_bind]
  | ok number =>
    by_cases valid : 0 ≤ number ∧ number < 256 <;>
      simp [Mutable.byte, paired, converted, eval_bind, valid, error]

/-- Every completed indexed write preserves the object count and returns only None on success. -/
theorem setItem_effect (heap after : Heap) (receiver index value : Value) (outcome : Except ExceptionObject Value)
    (executed : Mutable.setItem receiver index value heap = some (outcome, after)) :
    after.length = heap.length ∧ ∀ returned, outcome = .ok returned → returned = .scalar .none := by
  cases receiver with
  | scalar scalar =>
    simp [Mutable.setItem, error] at executed
    rcases executed with ⟨rfl, rfl⟩
    simp
  | ref address =>
    cases found : heap[address]? with
    | none => simp [Mutable.setItem, found, unsupported] at executed
    | some object =>
      cases object with
      | list items =>
        obtain ⟨result, indexed, _⟩ := index_total items index heap
        cases result <;> simp [Mutable.setItem, found, indexed, eval_bind, Except.map] at executed <;>
          rcases executed with ⟨rfl, rfl⟩ <;> simp
      | bytearray bytes =>
        obtain ⟨converted, convertedAt⟩ := integer_total heap index
        cases converted with
        | error exception =>
          simp [Mutable.setItem, found, convertedAt, eval_bind] at executed
          rcases executed with ⟨rfl, rfl⟩
          simp
        | ok number =>
          obtain ⟨converted, byteAt⟩ := byte_total heap value
          cases converted with
          | error exception =>
            simp [Mutable.setItem, found, convertedAt, byteAt, eval_bind] at executed
            rcases executed with ⟨rfl, rfl⟩
            simp
          | ok byte =>
            obtain ⟨position, indexed, _⟩ := index_total bytes (.scalar (.int number)) heap
            cases position <;> simp [Mutable.setItem, found, convertedAt, byteAt, indexed, eval_bind, Except.map] at executed <;>
              rcases executed with ⟨rfl, rfl⟩ <;> simp
      | dict entries =>
        cases index with
        | scalar key =>
          simp [Mutable.setItem, found, Except.map] at executed
          rcases executed with ⟨rfl, rfl⟩
          simp
        | ref keyAddress =>
          cases resolved : Mutable.keyOf heap (.ref keyAddress) with
          | none => simp [Mutable.setItem, found, hashKey, resolved, eval_bind] at executed
          | some result =>
            cases result <;> simp [Mutable.setItem, found, hashKey, resolved, eval_bind, Except.map] at executed <;>
              rcases executed with ⟨rfl, rfl⟩ <;> simp
      | keyDict entries =>
        cases resolved : Mutable.keyOf heap index with
        | none => simp [Mutable.setItem, found, hashKey, resolved, eval_bind] at executed
        | some result =>
          cases result <;> simp [Mutable.setItem, found, hashKey, resolved, eval_bind, Except.map] at executed <;>
            rcases executed with ⟨rfl, rfl⟩ <;> simp
      | _ =>
        simp [Mutable.setItem, found, error] at executed
        rcases executed with ⟨rfl, rfl⟩
        simp

theorem setItem_buffer_total (heap : Heap) (address : Nat) (bytes : List UInt8) (index value : Value)
    (found : heap[address]? = some (.bytearray bytes)) :
    ∃ outcome after, Mutable.setItem (.ref address) index value heap = some (outcome, after) := by
  obtain ⟨converted, convertedAt⟩ := integer_total heap index
  cases converted with
  | error exception => exact ⟨.error exception, heap, by simp [Mutable.setItem, found, convertedAt, eval_bind]⟩
  | ok number =>
    obtain ⟨converted, byteAt⟩ := byte_total heap value
    cases converted with
    | error exception => exact ⟨.error exception, heap, by simp [Mutable.setItem, found, convertedAt, byteAt, eval_bind]⟩
    | ok byte =>
      obtain ⟨position, indexed, _⟩ := index_total bytes (.scalar (.int number)) heap
      cases position with
      | error exception =>
        exact ⟨.error exception, heap, by simp [Mutable.setItem, found, convertedAt, byteAt, indexed, eval_bind]⟩
      | ok position =>
        exact ⟨.ok (.scalar .none), heap.set address (.bytearray (bytes.set position byte)), by
          simp [Mutable.setItem, found, convertedAt, byteAt, indexed, eval_bind, Except.map]⟩

theorem ExecutionLayout.setItem_buffer {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (address : Nat) (bytes : List UInt8) (index value : Value)
    (found : logical[address]? = some (.bytearray bytes)) (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.setItem (.ref address) index value logical = some (outcome, after)) :
    ∃ other, Mutable.setItem (.ref (rename address)) (relocateValue rename index) (relocateValue rename value) physical =
        some (outcome.map (relocateValue rename), other) ∧ ExecutionLayout after other rename := by
  have moved := layout.runtime.lookup address _ found
  have convertedPair := integer_relocates logical physical rename index
  have bytePair := byte_relocates logical physical rename value
  obtain ⟨converted, convertedAt⟩ := integer_total logical index
  cases converted with
  | error exception =>
    simp [Mutable.setItem, found, convertedAt, eval_bind] at executed
    rcases executed with ⟨rfl, rfl⟩
    refine ⟨physical, ?_, layout⟩
    simp [Mutable.setItem, moved, relocateObject, convertedPair, convertedAt, eval_bind, Except.map]
  | ok number =>
    obtain ⟨converted, byteAt⟩ := byte_total logical value
    cases converted with
    | error exception =>
      simp [Mutable.setItem, found, convertedAt, byteAt, eval_bind] at executed
      rcases executed with ⟨rfl, rfl⟩
      refine ⟨physical, ?_, layout⟩
      simp [Mutable.setItem, moved, relocateObject, convertedPair, convertedAt, bytePair, byteAt, eval_bind, Except.map]
    | ok byte =>
      have indexPair := index_relocates bytes bytes rfl (.scalar (.int number)) rename logical physical
      simp only [relocateValue] at indexPair
      obtain ⟨position, indexed, _⟩ := index_total bytes (.scalar (.int number)) logical
      cases position with
      | error exception =>
        simp [Mutable.setItem, found, convertedAt, byteAt, indexed, eval_bind] at executed
        rcases executed with ⟨rfl, rfl⟩
        refine ⟨physical, ?_, layout⟩
        simp [Mutable.setItem, moved, relocateObject, convertedPair, convertedAt, bytePair, byteAt,
          indexPair, indexed, eval_bind, Except.map]
      | ok position =>
        simp [Mutable.setItem, found, convertedAt, byteAt, indexed, eval_bind, Except.map] at executed
        rcases executed with ⟨rfl, rfl⟩
        refine ⟨physical.set (rename address) (.bytearray (bytes.set position byte)), ?_, ?_⟩
        · change Mutable.setItem (.ref (rename address)) (relocateValue rename index) (relocateValue rename value) physical =
            some (.ok (.scalar .none), _)
          simp [Mutable.setItem, moved, relocateObject, convertedPair, convertedAt, bytePair, byteAt,
            indexPair, indexed, eval_bind, Except.map]
        · exact layout.set_nonempty address _ _ found (by simp) (by simp) (by simp [ObjectWithin, objectValues])

theorem ExecutionLayout.setItem {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (receiver index value : Value)
    (receiverInside : receiver.edge.Within logical.length) (indexInside : index.edge.Within logical.length)
    (valueInside : value.edge.Within logical.length) (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.setItem receiver index value logical = some (outcome, after)) :
    ∃ other, Mutable.setItem (relocateValue rename receiver) (relocateValue rename index)
        (relocateValue rename value) physical = some (outcome.map (relocateValue rename), other) ∧
      ExecutionLayout after other rename := by
  cases receiver with
  | scalar scalar =>
    simp [Mutable.setItem, error] at executed
    rcases executed with ⟨rfl, rfl⟩
    exact ⟨physical, by simp [Mutable.setItem, relocateValue, error, Except.map], layout⟩
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem receiverInside
    cases object : logical[address] with
    | list items =>
      obtain ⟨other, paired, retained, _, _⟩ := layout.setItem_list address items index value
        (found.trans (congrArg some object)) valueInside outcome after executed
      exact ⟨other, paired, retained⟩
    | bytearray bytes =>
      exact layout.setItem_buffer address bytes index value (found.trans (congrArg some object)) outcome after executed
    | dict entries =>
      obtain ⟨other, paired, retained, _, _⟩ := layout.setItem_dict address entries index value
        (found.trans (congrArg some object)) indexInside valueInside outcome after executed
      exact ⟨other, paired, retained⟩
    | keyDict entries =>
      obtain ⟨other, paired, retained, _, _⟩ := layout.setItem_keyDict address entries index value
        (found.trans (congrArg some object)) indexInside valueInside outcome after executed
      exact ⟨other, paired, retained⟩
    | _ =>
      have actual := found.trans (congrArg some object)
      have moved := layout.runtime.lookup address _ actual
      simp [Mutable.setItem, actual, error] at executed
      rcases executed with ⟨rfl, rfl⟩
      exact ⟨physical, by simp [Mutable.setItem, relocateValue, moved, relocateObject, error, Except.map], layout⟩

theorem RuntimeLayout.setItem_unsupported {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical) (receiver index value : Value)
    (receiverInside : receiver.edge.Within logical.length) (indexInside : index.edge.Within logical.length) :
    Mutable.setItem (relocateValue rename receiver) (relocateValue rename index) (relocateValue rename value) physical = none ↔
      Mutable.setItem receiver index value logical = none := by
  cases receiver with
  | scalar scalar => simp [Mutable.setItem, relocateValue, error]
  | ref address =>
    change Mutable.setItem (.ref (rename address)) (relocateValue rename index) (relocateValue rename value) physical = none ↔ _
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem receiverInside
    cases object : logical[address] with
    | list items =>
      have actual := found.trans (congrArg some object)
      have moved := layout.lookup address _ actual
      have paired := index_relocates items (items.map (relocateValue rename)) (by simp) index rename logical physical
      obtain ⟨outcome, indexed, _⟩ := index_total items index logical
      cases outcome <;> simp [Mutable.setItem, actual, moved, relocateObject, paired, indexed, eval_bind, Except.map]
    | bytearray bytes =>
      have actual := found.trans (congrArg some object)
      have moved : physical[rename address]? = some (.bytearray bytes) := layout.lookup address _ actual
      obtain ⟨left, after, first⟩ := setItem_buffer_total logical address bytes index value actual
      obtain ⟨right, other, second⟩ := setItem_buffer_total physical (rename address) bytes
        (relocateValue rename index) (relocateValue rename value) moved
      simp [first, second]
    | dict entries =>
      exact layout.setItem_dict_unsupported closed address entries index value (found.trans (congrArg some object)) indexInside
    | keyDict entries =>
      exact layout.setItem_keyDict_unsupported closed address entries index value (found.trans (congrArg some object)) indexInside
    | _ =>
      have actual := found.trans (congrArg some object)
      have moved := layout.lookup address _ actual
      simp [Mutable.setItem, actual, moved, relocateObject, error]

end FormalSW.PyAst.Mutable.Relocation
