import lang.py.FormalSW.MachineAllocation
import lang.py.FormalSW.ConstructionRelocation

/-! A common interface for completed primitives that may allocate or mutate objects. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

/-- A completed logical evaluation derives its physical counterpart and an extending address map.
This forward property does not assert that unsupported or divergent evaluations complete. -/
def EvalRelocates (logical physical : Heap) (rename : Nat → Nat) (action otherAction : Eval Value) : Prop :=
  ∀ outcome after, action logical = some (outcome, after) →
    ∃ other nextMap,
      otherAction physical = some (outcome.map (relocateValue nextMap), other) ∧
      ExecutionLayout after other nextMap ∧
      (∀ address < logical.length, nextMap address = rename address) ∧
      logical.length ≤ after.length ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length)

theorem EvalRelocates.congr {logical physical : Heap} {rename : Nat → Nat}
    {action otherAction first second : Eval Value} (related : EvalRelocates logical physical rename action otherAction)
    (left : first logical = action logical) (right : second physical = otherAction physical) :
    EvalRelocates logical physical rename first second := by
  intro outcome after executed
  obtain ⟨other, nextMap, paired, retained⟩ := related outcome after (left ▸ executed)
  exact ⟨other, nextMap, right.trans paired, retained⟩

theorem ExecutionLayout.pure_relocates {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (value : Value) (inside : value.edge.Within logical.length) :
    EvalRelocates logical physical rename (pure value) (pure (relocateValue rename value)) := by
  intro outcome after executed
  have same : Except.ok value = outcome ∧ logical = after := by simpa using executed
  obtain ⟨rfl, rfl⟩ := same
  refine ⟨physical, rename, rfl, layout, fun _ _ => rfl, Nat.le_refl _, ?_⟩
  intro returned equal
  cases equal
  exact inside

theorem ExecutionLayout.throw_relocates {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (exception : ExceptionObject) :
    EvalRelocates logical physical rename (throw exception) (throw exception) := by
  intro outcome after executed
  have same : Except.error exception = outcome ∧ logical = after := by simpa using executed
  obtain ⟨rfl, rfl⟩ := same
  refine ⟨physical, rename, rfl, layout, fun _ _ => rfl, Nat.le_refl _, ?_⟩
  intro value impossible
  cases impossible

theorem unsupported_relocates (logical physical : Heap) (rename : Nat → Nat) :
    EvalRelocates logical physical rename unsupported unsupported := by
  intro outcome after executed
  simp [unsupported] at executed

/-- A read-only conversion can feed an allocating or mutating action, retaining early exceptions. -/
theorem EvalRelocates.readonly_bind {α : Type} {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (read otherRead : Eval α) (next otherNext : α → Eval Value)
    (paired : otherRead physical = (read logical).map (fun result => (result.1, physical)))
    (unchanged : ∀ outcome after, read logical = some (outcome, after) → after = logical)
    (following : ∀ value, read logical = some (.ok value, logical) →
      EvalRelocates logical physical rename (next value) (otherNext value)) :
    EvalRelocates logical physical rename (read >>= next) (otherRead >>= otherNext) := by
  intro outcome after executed
  cases tested : read logical with
  | none => simp [tested, eval_bind] at executed
  | some pair =>
    rcases pair with ⟨result, middle⟩
    have same := unchanged result middle tested
    subst middle
    cases result with
    | error exception =>
      have equal : Except.error exception = outcome ∧ logical = after := by
        simpa [tested, eval_bind] using executed
      obtain ⟨rfl, rfl⟩ := equal
      refine ⟨physical, rename, ?_, layout, fun _ _ => rfl, Nat.le_refl _, ?_⟩
      · simp [paired, tested, eval_bind, Except.map]
      · intro value impossible
        cases impossible
    | ok value =>
      have continued : next value logical = some (outcome, after) := by simpa [tested, eval_bind] using executed
      obtain ⟨other, nextMap, completed, rest⟩ := following value tested outcome after continued
      refine ⟨other, nextMap, ?_, rest⟩
      simpa [paired, tested, eval_bind] using completed

theorem ExecutionLayout.allocate_list_relocates {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (items : List Value)
    (inside : ∀ value ∈ items, value.edge.Within logical.length) :
    EvalRelocates logical physical rename (Mutable.allocate items) (Mutable.allocate (items.map (relocateValue rename))) := by
  intro outcome after executed
  obtain ⟨first, second, retained⟩ := layout.allocate_list items inside
  rw [first] at executed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
  refine ⟨_, extendMap rename logical.length physical.length, ?_, retained,
    extendMap_old rename logical.length physical.length, by simp, ?_⟩
  · simpa only [Except.map, relocateValue, extendMap_new] using second
  · intro returned same
    cases same
    simp [Value.edge, Graph.Edge.Within]

theorem ExecutionLayout.allocateTuple_relocates {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (items : List Value)
    (inside : ∀ value ∈ items, value.edge.Within logical.length) :
    EvalRelocates logical physical rename (Mutable.allocateTuple items)
      (Mutable.allocateTuple (items.map (relocateValue rename))) := by
  intro outcome after executed
  obtain ⟨left, right, logicalAfter, physicalAfter, nextMap, first, second, retained, bounded, same, agree⟩ :=
    layout.allocateTuple items inside
  rw [first] at executed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
  refine ⟨physicalAfter, nextMap, ?_, retained, agree,
    HeapCalls.Relocation.allocateTuple_length logical logicalAfter items (.ref left) first, ?_⟩
  · simpa only [Except.map, relocateValue, same] using second
  · intro returned equal
    cases equal
    exact bounded

theorem ExecutionLayout.allocateBuffer_relocates {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (bytes : List UInt8) :
    EvalRelocates logical physical rename (Mutable.allocateBuffer bytes) (Mutable.allocateBuffer bytes) := by
  intro outcome after executed
  obtain ⟨first, second, retained⟩ := layout.allocateBuffer bytes
  rw [first] at executed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
  refine ⟨_, extendMap rename logical.length physical.length, ?_, retained,
    extendMap_old rename logical.length physical.length, by simp, ?_⟩
  · simpa only [Except.map, relocateValue, extendMap_new] using second
  · intro returned equal
    cases equal
    simp [Value.edge, Graph.Edge.Within]

theorem replicated_values_within (limit count : Nat) (items : List Value)
    (inside : ∀ value ∈ items, value.edge.Within limit) :
    ∀ value ∈ (List.replicate count items).flatten, value.edge.Within limit := by
  intro value member
  obtain ⟨row, copies, inRow⟩ := List.mem_flatten.mp member
  have same : row = items := (List.mem_replicate.mp copies).2
  exact inside value (same ▸ inRow)

theorem map_replicated_values (rename : Nat → Nat) (count : Nat) (items : List Value) :
    ((List.replicate count items).flatten).map (relocateValue rename) =
      (List.replicate count (items.map (relocateValue rename))).flatten := by
  simp only [List.map_flatten, List.map_replicate]

end FormalSW.PyAst.Mutable.Relocation
