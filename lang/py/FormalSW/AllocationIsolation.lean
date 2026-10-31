import lang.py.FormalSW.ConstructionRelocation
import lang.py.FormalSW.AllocationFrame

/-! Allocation preserves protected objects while accounting for empty-tuple interning. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

/-- The protected object remains outside the caller's address image. -/
structure PrivateLayout (logical physical : Heap) (rename : Nat → Nat) (address : Nat) (object : Object) : Prop where
  layout : ExecutionLayout logical physical rename
  saved : SavedCell address object physical
  excludes : ∀ source < logical.length, rename source ≠ address

theorem extendMap_excludes (rename : Nat → Nat) (logicalSize physicalSize address : Nat)
    (outside : ∀ source < logicalSize, rename source ≠ address) (old : address < physicalSize) :
    ∀ source < logicalSize + 1, extendMap rename logicalSize physicalSize source ≠ address := by
  intro source bounded
  by_cases fresh : source = logicalSize
  · subst source
    simpa only [extendMap_new] using Nat.ne_of_gt old
  · have previous : source < logicalSize := by omega
    simpa only [extendMap_old _ _ _ _ previous] using outside source previous

theorem PrivateLayout.preserves {logical physical : Heap} {rename : Nat → Nat} {address : Nat} {object : Object}
    (before : PrivateLayout logical physical rename address object) (logicalAfter physicalAfter : Heap)
    (layout : ExecutionLayout logicalAfter physicalAfter rename) (same : logicalAfter.length = logical.length)
    (saved : SavedCell address object physicalAfter) : PrivateLayout logicalAfter physicalAfter rename address object :=
  ⟨layout, saved, fun source bounded => before.excludes source (by simpa only [same] using bounded)⟩

theorem PrivateLayout.append_object {logical physical : Heap} {rename : Nat → Nat} {address : Nat} {object : Object}
    (before : PrivateLayout logical physical rename address object) (fresh : Object)
    (nonempty : fresh ≠ .tuple []) (inside : ObjectWithin (logical.length + 1) fresh) :
    PrivateLayout (logical ++ [fresh])
      (physical ++ [relocateObject (extendMap rename logical.length physical.length) fresh])
      (extendMap rename logical.length physical.length) address object := by
  refine ⟨before.layout.append_object fresh nonempty inside,
    SavedCell.append address object _ _ before.saved, ?_⟩
  simpa only [List.length_append, List.length_singleton] using
    extendMap_excludes rename logical.length physical.length address before.excludes
      (List.getElem?_eq_some_iff.mp before.saved).1

theorem PrivateLayout.append_existing {logical physical : Heap} {rename : Nat → Nat} {address : Nat} {object : Object}
    (before : PrivateLayout logical physical rename address object) (fresh : Object)
    (nonempty : fresh ≠ .tuple []) (inside : ObjectWithin logical.length fresh) :
    PrivateLayout (logical ++ [fresh]) (physical ++ [relocateObject rename fresh])
      (extendMap rename logical.length physical.length) address object := by
  have same := relocateObject_congr (extendMap rename logical.length physical.length) rename
    logical.length fresh (fun _ bound => extendMap_old _ _ _ _ bound) inside
  simpa only [same] using before.append_object fresh nonempty (inside.mono (by omega))

theorem PrivateLayout.allocate_list {logical physical : Heap} {rename : Nat → Nat} {address : Nat} {object : Object}
    (before : PrivateLayout logical physical rename address object)
    (items : List Value) (inside : ∀ value ∈ items, value.edge.Within logical.length) :
    Mutable.allocate items logical = some (.ok (.ref logical.length), logical ++ [.list items]) ∧
    Mutable.allocate (items.map (relocateValue rename)) physical =
      some (.ok (.ref physical.length), physical ++ [.list (items.map (relocateValue rename))]) ∧
    PrivateLayout (logical ++ [.list items]) (physical ++ [.list (items.map (relocateValue rename))])
      (extendMap rename logical.length physical.length) address object :=
  ⟨rfl, rfl, before.append_existing (.list items) (by simp) inside⟩

theorem PrivateLayout.allocateSet {logical physical : Heap} {rename : Nat → Nat} {address : Nat} {object : Object}
    (before : PrivateLayout logical physical rename address object) (items : List Constant) :
    Mutable.allocateSet items logical = some (.ok (.ref logical.length), logical ++ [.set items]) ∧
    Mutable.allocateSet items physical = some (.ok (.ref physical.length), physical ++ [.set items]) ∧
    PrivateLayout (logical ++ [.set items]) (physical ++ [.set items])
      (extendMap rename logical.length physical.length) address object :=
  ⟨rfl, rfl, before.append_existing (.set items) (by simp) (by simp [ObjectWithin, objectValues])⟩

theorem PrivateLayout.allocateBuffer {logical physical : Heap} {rename : Nat → Nat} {address : Nat} {object : Object}
    (before : PrivateLayout logical physical rename address object) (bytes : List UInt8) :
    Mutable.allocateBuffer bytes logical = some (.ok (.ref logical.length), logical ++ [.bytearray bytes]) ∧
    Mutable.allocateBuffer bytes physical = some (.ok (.ref physical.length), physical ++ [.bytearray bytes]) ∧
    PrivateLayout (logical ++ [.bytearray bytes]) (physical ++ [.bytearray bytes])
      (extendMap rename logical.length physical.length) address object :=
  ⟨rfl, rfl, before.append_existing (.bytearray bytes) (by simp) (by simp [ObjectWithin, objectValues])⟩

theorem PrivateLayout.allocateDict {logical physical : Heap} {rename : Nat → Nat} {address : Nat} {object : Object}
    (before : PrivateLayout logical physical rename address object)
    (entries : List (Constant × Value)) (inside : ObjectWithin logical.length (.dict entries)) :
    Mutable.allocateDict entries logical = some (.ok (.ref logical.length), logical ++ [.dict entries]) ∧
    Mutable.allocateDict (entries.map fun entry => (entry.1, relocateValue rename entry.2)) physical =
      some (.ok (.ref physical.length), physical ++ [.dict (entries.map fun entry => (entry.1, relocateValue rename entry.2))]) ∧
    PrivateLayout (logical ++ [.dict entries])
      (physical ++ [.dict (entries.map fun entry => (entry.1, relocateValue rename entry.2))])
      (extendMap rename logical.length physical.length) address object :=
  ⟨rfl, rfl, before.append_existing (.dict entries) (by simp) inside⟩

theorem PrivateLayout.allocateInstance {logical physical : Heap} {rename : Nat → Nat} {address : Nat} {object : Object}
    (before : PrivateLayout logical physical rename address object) (origin name : String) :
    Mutable.allocateInstance origin name logical = some (.ok (.ref logical.length), logical ++ [.instance origin name []]) ∧
    Mutable.allocateInstance origin name physical = some (.ok (.ref physical.length), physical ++ [.instance origin name []]) ∧
    PrivateLayout (logical ++ [.instance origin name []]) (physical ++ [.instance origin name []])
      (extendMap rename logical.length physical.length) address object :=
  ⟨rfl, rfl, before.append_existing (.instance origin name []) (by simp) (by simp [ObjectWithin, objectValues])⟩

/-- The tuple allocator either reuses an empty tuple or appends exactly its result object. -/
theorem allocateTuple_shape (heap after : Heap) (items : List Value) (address : Nat)
    (executed : Mutable.allocateTuple items heap = some (.ok (.ref address), after)) :
    (after = heap ∧ heap[address]? = some (.tuple [])) ∨
      (address = heap.length ∧ after = heap ++ [.tuple items]) := by
  cases items with
  | nil =>
    cases found : emptyTupleAddress heap with
    | none =>
      simp only [emptyTupleAddress] at found
      simp [Mutable.allocateTuple, found, Except.map] at executed
      obtain ⟨rfl, rfl⟩ := executed
      exact Or.inr ⟨rfl, rfl⟩
    | some selected =>
      have stored := emptyTupleAddress_lookup found
      simp only [emptyTupleAddress] at found
      simp [Mutable.allocateTuple, found] at executed
      obtain ⟨rfl, rfl⟩ := executed
      exact Or.inl ⟨rfl, stored⟩
  | cons first rest =>
    simp [Mutable.allocateTuple, Except.map] at executed
    obtain ⟨rfl, rfl⟩ := executed
    exact Or.inr ⟨rfl, rfl⟩

theorem allocateTuple_new_address (heap after : Heap) (items : List Value) (address source : Nat)
    (executed : Mutable.allocateTuple items heap = some (.ok (.ref address), after))
    (new : heap.length ≤ source) (bounded : source < after.length) : source = address := by
  rcases allocateTuple_shape heap after items address executed with ⟨rfl, _⟩ | ⟨rfl, rfl⟩
  · omega
  · simp only [List.length_append, List.length_singleton] at bounded
    omega

theorem allocateTuple_result_separate (heap after : Heap) (items : List Value) (result address : Nat) (object : Object)
    (executed : Mutable.allocateTuple items heap = some (.ok (.ref result), after))
    (saved : SavedCell address object heap) (nonempty : object ≠ .tuple []) : result ≠ address := by
  rcases allocateTuple_shape heap after items result executed with ⟨_, interned⟩ | ⟨rfl, _⟩
  · intro same
    subst result
    rw [saved] at interned
    exact nonempty (Option.some.inj interned)
  · exact Nat.ne_of_gt (List.getElem?_eq_some_iff.mp saved).1

/-- Every new logical tuple address is the allocator's returned address, so its mapped target is known. -/
theorem allocateTuple_map_excludes (logical physical logicalAfter physicalAfter : Heap)
    (rename nextMap : Nat → Nat) (items : List Value) (left right address : Nat) (object : Object)
    (leftRun : Mutable.allocateTuple items logical = some (.ok (.ref left), logicalAfter))
    (rightRun : Mutable.allocateTuple (items.map (relocateValue rename)) physical = some (.ok (.ref right), physicalAfter))
    (same : nextMap left = right) (agree : ∀ source < logical.length, nextMap source = rename source)
    (outside : ∀ source < logical.length, rename source ≠ address)
    (saved : SavedCell address object physical) (nonempty : object ≠ .tuple []) :
    ∀ source < logicalAfter.length, nextMap source ≠ address := by
  intro source bounded
  by_cases old : source < logical.length
  · rw [agree source old]
    exact outside source old
  · have fresh := allocateTuple_new_address logical logicalAfter items left source leftRun (by omega) bounded
    rw [fresh, same]
    exact allocateTuple_result_separate physical physicalAfter _ right address object rightRun saved nonempty

theorem PrivateLayout.allocateTuple {logical physical : Heap} {rename : Nat → Nat} {address : Nat} {object : Object}
    (before : PrivateLayout logical physical rename address object) (nonempty : object ≠ .tuple [])
    (items : List Value) (inside : ∀ value ∈ items, value.edge.Within logical.length) :
    ∃ left right logicalAfter physicalAfter nextMap,
      Mutable.allocateTuple items logical = some (.ok (.ref left), logicalAfter) ∧
      Mutable.allocateTuple (items.map (relocateValue rename)) physical = some (.ok (.ref right), physicalAfter) ∧
      PrivateLayout logicalAfter physicalAfter nextMap address object ∧
      left < logicalAfter.length ∧ nextMap left = right ∧
      (∀ source < logical.length, nextMap source = rename source) := by
  obtain ⟨left, right, logicalAfter, physicalAfter, nextMap, leftRun, rightRun, layout, bounded, same, agree⟩ :=
    before.layout.allocateTuple items inside
  have retained := Heapq.preserves_allocateTuple (SavedCell address object) (SavedCell.allocates address object)
    (items.map (relocateValue rename)) physical (.ok (.ref right)) physicalAfter before.saved rightRun
  exact ⟨left, right, logicalAfter, physicalAfter, nextMap, leftRun, rightRun,
    ⟨layout, retained, allocateTuple_map_excludes logical physical logicalAfter physicalAfter rename nextMap items
      left right address object leftRun rightRun same agree before.excludes before.saved nonempty⟩,
    bounded, same, agree⟩

end FormalSW.PyAst.Mutable.Relocation
