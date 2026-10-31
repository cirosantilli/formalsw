import lang.py.FormalSW.ItemWriteRelocation

/-! List and buffer mutations retain live contents and exact index-conversion outcomes. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

/-- Append is total on bounded receivers in the current model, including byte conversion errors. -/
theorem ExecutionLayout.appendItem {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (address : Nat) (value : Value)
    (addressInside : address < logical.length) (valueInside : value.edge.Within logical.length) :
    ∃ outcome after other,
      Mutable.appendItem address value logical = some (outcome, after) ∧
      Mutable.appendItem (rename address) (relocateValue rename value) physical =
        some (outcome.map (relocateValue rename), other) ∧
      ExecutionLayout after other rename ∧ after.length = logical.length ∧ other.length = physical.length ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem addressInside
  have moved := layout.runtime.lookup address _ found
  cases object : logical[address] <;> simp only [object, relocateObject] at moved
  case list items =>
    obtain ⟨left, right, retained⟩ := layout.appendItem_list address items value
      (found.trans (congrArg some object)) valueInside
    exact ⟨.ok (.scalar .none), _, _, left, right, retained, by simp, by simp,
      by intro returned same; cases same; trivial⟩
  case bytearray bytes =>
    have paired := byte_relocates logical physical rename value
    obtain ⟨outcome, converted⟩ := byte_total logical value
    cases outcome with
    | error exception =>
      refine ⟨.error exception, logical, physical, ?_, ?_, layout, rfl, rfl, ?_⟩
      · simp [Mutable.appendItem, found, object, converted, eval_bind]
      · simp [Mutable.appendItem, moved, paired, converted, eval_bind, Except.map]
      · intro returned impossible; cases impossible
    | ok byte =>
      have retained := layout.set_nonempty address _ (.bytearray (bytes ++ [byte]))
        (found.trans (congrArg some object)) (by simp) (by simp) (by simp [ObjectWithin, objectValues])
      refine ⟨.ok (.scalar .none), _, _, ?_, ?_, retained, by simp, by simp, ?_⟩
      · simp [Mutable.appendItem, found, object, converted, eval_bind, Except.map]
      · simp [Mutable.appendItem, moved, paired, converted, eval_bind, Except.map, relocateObject]
        rfl
      · intro returned same; cases same; trivial
  all_goals
    refine ⟨.error ⟨"AttributeError", []⟩, logical, physical, ?_, ?_, layout, rfl, rfl, ?_⟩
    · simp [Mutable.appendItem, found, object, error]
    · simp [Mutable.appendItem, moved, error, Except.map]
    · intro returned impossible; cases impossible

/-- Index protocols must be checked before inspecting the live pop receiver. -/
def popIndex (subscript : Value) : Eval Int :=
  match subscript with
  | .ref address => do
      match (← get)[address]? with
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => unsupported
      | some _ => error "TypeError"
      | none => unsupported
  | _ => integer subscript

theorem popItem_index (heap : Heap) (address : Nat) (subscript : Value) :
    Mutable.popItem address subscript heap =
      (do let position ← popIndex subscript; Mutable.popItem address (.scalar (.int position))) heap := by
  cases subscript with
  | scalar scalar => cases scalar <;> rfl
  | ref indexAddress =>
    cases found : heap[indexAddress]? with
    | none => simp [Mutable.popItem, popIndex, found, unsupported, eval_bind]
    | some object => cases object <;> simp [Mutable.popItem, popIndex, found, unsupported, error, eval_bind]

theorem RuntimeLayout.popIndex_relocates {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (subscript : Value) (inside : subscript.edge.Within logical.length) :
    popIndex (relocateValue rename subscript) physical =
      (popIndex subscript logical).map (fun pair => (pair.1, physical)) := by
  cases subscript with
  | scalar scalar => exact integer_relocates logical physical rename (.scalar scalar)
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;> simp only [object, relocateObject] at moved
    all_goals simp [popIndex, relocateValue, found, object, moved, unsupported, error]

theorem popIndex_heap (heap after : Heap) (subscript : Value) (outcome : Except ExceptionObject Int)
    (executed : popIndex subscript heap = some (outcome, after)) : after = heap := by
  cases subscript with
  | scalar scalar =>
    obtain ⟨answer, converted⟩ := integer_total heap (.scalar scalar)
    have same : answer = outcome ∧ heap = after := by simpa [popIndex, converted] using executed
    exact same.2.symm
  | ref address =>
    cases found : heap[address]? with
    | none => simp [popIndex, found, unsupported] at executed
    | some object =>
      cases object <;> simp [popIndex, found, unsupported, error] at executed
      all_goals exact executed.2.symm

/-- Select the removed occurrence and remaining references, with no index cutoff. -/
def popSelection {α : Type} (items : List α) (index : Int) : Option (α × List α) := do
  let position ← Py.Builtin.Sequence.normalizeIndex items.length index
  let value ← items[position]?
  pure (value, items.take position ++ items.drop (position + 1))

theorem popSelection_map {α β : Type} (items : List α) (index : Int) (move : α → β) :
    popSelection (items.map move) index = (popSelection items index).map (fun pair => (move pair.1, pair.2.map move)) := by
  unfold popSelection
  cases normalized : Py.Builtin.Sequence.normalizeIndex items.length index with
  | none => simp [normalized]
  | some position =>
    cases selected : items[position]? <;> simp [normalized, selected, List.map_append, List.map_take, List.map_drop]

theorem popSelection_members {α : Type} (items : List α) (index : Int) (value : α) (remaining : List α)
    (selected : popSelection items index = some (value, remaining)) :
    value ∈ items ∧ ∀ item ∈ remaining, item ∈ items := by
  unfold popSelection at selected
  cases normalized : Py.Builtin.Sequence.normalizeIndex items.length index with
  | none => simp [normalized] at selected
  | some position =>
    cases found : items[position]? with
    | none => simp [normalized, found] at selected
    | some present =>
      simp [normalized, found] at selected
      rcases selected with ⟨rfl, rfl⟩
      refine ⟨List.mem_of_getElem? found, ?_⟩
      intro item member
      rcases List.mem_append.mp member with before | after
      · exact List.mem_of_mem_take before
      · exact List.mem_of_mem_drop after

theorem list_popSelection {α : Type} (items : List α) (index : Int) :
    Py.Builtin.List.pop items index = match popSelection items index with
      | none => .error (.indexError "pop index out of range")
      | some pair => .ok pair := by
  unfold popSelection
  cases normalized : Py.Builtin.Sequence.normalizeIndex items.length index with
  | none => simp [Py.Builtin.List.pop, normalized, bind, pure, Except.bind]
  | some position =>
    cases selected : items[position]? <;> simp [Py.Builtin.List.pop, normalized, selected, bind, pure, Except.bind, Except.pure]

theorem popItem_list_selection (heap : Heap) (address : Nat) (items : List Value) (index : Int)
    (found : heap[address]? = some (.list items)) :
    Mutable.popItem address (.scalar (.int index)) heap =
      match popSelection items index with
      | none => some (.error ⟨"IndexError", []⟩, heap)
      | some (value, remaining) => some (.ok value, heap.set address (.list remaining)) := by
  simp only [Mutable.popItem, integer, eval_bind, eval_pure, eval_get, Option.bind_eq_bind, Option.bind_some,
    found, list_popSelection]
  cases selected : popSelection items index with
  | none => rfl
  | some pair => rcases pair with ⟨value, remaining⟩; rfl

theorem popItem_buffer_selection (heap : Heap) (address : Nat) (bytes : List UInt8) (index : Int)
    (found : heap[address]? = some (.bytearray bytes)) :
    Mutable.popItem address (.scalar (.int index)) heap =
      match popSelection bytes index with
      | none => some (.error ⟨"IndexError", []⟩, heap)
      | some (value, remaining) => some (.ok (.scalar (.int value.toNat)), heap.set address (.bytearray remaining)) := by
  simp only [Mutable.popItem, integer, eval_bind, eval_pure, eval_get, Option.bind_eq_bind, Option.bind_some,
    found, list_popSelection]
  cases selected : popSelection bytes index with
  | none => rfl
  | some pair => rcases pair with ⟨value, remaining⟩; rfl

theorem ExecutionLayout.popItem_integer {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (address : Nat) (index : Int) (addressInside : address < logical.length) :
    ∃ outcome after other,
      Mutable.popItem address (.scalar (.int index)) logical = some (outcome, after) ∧
      Mutable.popItem (rename address) (.scalar (.int index)) physical =
        some (outcome.map (relocateValue rename), other) ∧
      ExecutionLayout after other rename ∧ after.length = logical.length ∧ other.length = physical.length ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem addressInside
  have moved := layout.runtime.lookup address _ found
  have old := layout.closed _ (List.mem_of_getElem? found)
  cases object : logical[address] <;> simp only [object, relocateObject] at moved
  case list items =>
    rw [object] at found old
    rw [popItem_list_selection logical address items index found,
      popItem_list_selection physical (rename address) _ index moved, popSelection_map]
    cases selected : popSelection items index with
    | none => exact ⟨.error ⟨"IndexError", []⟩, logical, physical, rfl, rfl, layout, rfl, rfl, by intro _ impossible; cases impossible⟩
    | some pair =>
      rcases pair with ⟨value, remaining⟩
      have members := popSelection_members items index value remaining selected
      have retained := layout.set_list address items remaining found (fun item member => old item (members.2 item member))
      refine ⟨.ok value, _, _, rfl, rfl, retained, by simp, by simp, ?_⟩
      intro returned same
      cases same
      simpa using old value members.1
  case bytearray bytes =>
    rw [object] at found
    rw [popItem_buffer_selection logical address bytes index found,
      popItem_buffer_selection physical (rename address) bytes index moved]
    cases selected : popSelection bytes index with
    | none => exact ⟨.error ⟨"IndexError", []⟩, logical, physical, rfl, rfl, layout, rfl, rfl, by intro _ impossible; cases impossible⟩
    | some pair =>
      rcases pair with ⟨value, remaining⟩
      have retained := layout.set_nonempty address _ (.bytearray remaining) found (by simp) (by simp)
        (by simp [ObjectWithin, objectValues])
      refine ⟨.ok (.scalar (.int value.toNat)), _, _, rfl, rfl, retained, by simp, by simp, ?_⟩
      intro returned same; cases same; trivial
  all_goals
    refine ⟨.error ⟨"AttributeError", []⟩, logical, physical, ?_, ?_, layout, rfl, rfl, ?_⟩
    · simp [Mutable.popItem, integer, found, object, error, eval_bind]
    · simp [Mutable.popItem, integer, moved, error, eval_bind, Except.map]
    · intro returned impossible; cases impossible

end FormalSW.PyAst.Mutable.Relocation
