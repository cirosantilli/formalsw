import lang.py.FormalSW.RuntimeRelocation
import lang.py.FormalSW.HeapCalls

/-! Tuple allocation preserves runtime layouts, including reuse of the empty tuple. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

def emptyTupleAddress (heap : Heap) : Option Nat :=
  heap.findIdx? (fun object => decide (object = .tuple []))

/-- The logical allocator's existing empty tuple must map to the physical allocator's choice.
The physical heap may also contain a private empty tuple when the logical heap has none. -/
def EmptyTuplesAligned (logical physical : Heap) (rename : Nat → Nat) : Prop :=
  ∀ address, emptyTupleAddress logical = some address →
    emptyTupleAddress physical = some (rename address)

theorem EmptyTuplesAligned.refl (heap : Heap) : EmptyTuplesAligned heap heap id :=
  fun _ found => found

/-- Writes to ordinary containers do not change which empty tuple is interned. -/
theorem emptyTupleAddress_set (heap : Heap) (address : Nat) (before after : Object)
    (found : heap[address]? = some before) (old : before ≠ .tuple [])
    (new : after ≠ .tuple []) :
    emptyTupleAddress (heap.set address after) = emptyTupleAddress heap := by
  induction heap generalizing address with
  | nil => simp at found
  | cons head tail ih =>
    cases address with
    | zero =>
      have same : head = before := by simpa using found
      subst head
      simp [emptyTupleAddress, List.findIdx?_cons, old, new]
    | succ address =>
      have remaining : tail[address]? = some before := by simpa using found
      simpa only [emptyTupleAddress, List.set_cons_succ, List.findIdx?_cons] using
        congrArg (fun result : Option Nat =>
          if decide (head = Object.tuple []) then some 0 else result.map Nat.succ)
          (ih address remaining)

theorem emptyTupleAddress_set_nonempty (heap : Heap) (address : Nat) (after : Object)
    (old : heap[address]? ≠ some (.tuple [])) (new : after ≠ .tuple []) :
    emptyTupleAddress (heap.set address after) = emptyTupleAddress heap := by
  cases found : heap[address]? with
  | none => rw [List.set_eq_of_length_le (List.getElem?_eq_none_iff.mp found)]
  | some before =>
    apply emptyTupleAddress_set heap address before after found _ new
    intro same
    exact old (same ▸ found)

theorem emptyTupleAddress_append_nonempty (heap : Heap) (object : Object)
    (nonempty : object ≠ .tuple []) :
    emptyTupleAddress (heap ++ [object]) = emptyTupleAddress heap := by
  simp [emptyTupleAddress, List.findIdx?_append, nonempty]

theorem EmptyTuplesAligned.preserves {logical physical after : Heap} {rename : Nat → Nat}
    (interned : EmptyTuplesAligned logical physical rename)
    (same : emptyTupleAddress after = emptyTupleAddress physical) :
    EmptyTuplesAligned logical after rename := by
  intro address found
  rw [same]
  exact interned address found

variable {logical physical : Heap} {rename : Nat → Nat}

theorem emptyTupleAddress_lookup {heap : Heap} {address : Nat}
    (found : emptyTupleAddress heap = some address) : heap[address]? = some (.tuple []) := by
  obtain ⟨inside, matching, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
  have equal : heap[address] = .tuple [] := by simpa using matching
  simpa [equal] using List.getElem?_eq_getElem inside

theorem emptyTupleAddress_absent {heap : Heap} (absent : emptyTupleAddress heap = none)
    (address : Nat) : heap[address]? ≠ some (.tuple []) := by
  intro found
  have excluded := List.findIdx?_eq_none_iff.mp absent (.tuple []) (List.mem_of_getElem? found)
  simp at excluded

@[simp] theorem relocateObject_emptyTuple (object : Object) :
    relocateObject rename object = .tuple [] ↔ object = .tuple [] := by
  cases object <;> simp [relocateObject]

/-- Reuse of a private immutable cell extends the map without appending to the physical heap. -/
theorem RuntimeLayout.reuse_private (layout : RuntimeLayout logical physical rename)
    (closed : Closed logical) (object : Object) (address : Nat)
    (separate : ∀ index < logical.length, rename index ≠ address)
    (found : physical[address]? =
      some (relocateObject (extendMap rename logical.length address) object)) :
    RuntimeLayout (logical ++ [object]) physical (extendMap rename logical.length address) := by
  constructor
  · intro i hi j hj equal
    simp only [List.length_append, List.length_singleton] at hi hj
    by_cases freshI : i = logical.length <;> by_cases freshJ : j = logical.length
    · omega
    · have oldJ : j < logical.length := by omega
      simp only [freshI, extendMap_new, extendMap_old _ _ _ _ oldJ] at equal
      exact False.elim (separate j oldJ equal.symm)
    · have oldI : i < logical.length := by omega
      simp only [freshJ, extendMap_new, extendMap_old _ _ _ _ oldI] at equal
      exact False.elim (separate i oldI equal)
    · have oldI : i < logical.length := by omega
      have oldJ : j < logical.length := by omega
      simp only [extendMap_old _ _ _ _ oldI, extendMap_old _ _ _ _ oldJ] at equal
      exact layout.injective i oldI j oldJ equal
  · intro index current lookup
    by_cases old : index < logical.length
    · have original : logical[index]? = some current := by
        simpa [List.getElem?_append, old] using lookup
      rw [extendMap_old _ _ _ _ old, layout.lookup index current original]
      congr 1
      exact relocateObject_congr _ _ logical.length current
        (fun i hi => (extendMap_old _ _ _ _ hi).symm)
        (closed current (List.mem_of_getElem? original))
    · have indexBound := (List.getElem?_eq_some_iff.mp lookup).1
      have equal : index = logical.length := by
        simp only [List.length_append, List.length_singleton] at indexBound
        omega
      subst index
      have same : current = object := by simpa using lookup.symm
      subst current
      simpa using found

theorem RuntimeLayout.private_emptyTuple (layout : RuntimeLayout logical physical rename)
    (absent : emptyTupleAddress logical = none) (address : Nat)
    (found : physical[address]? = some (.tuple [])) :
    ∀ index < logical.length, rename index ≠ address := by
  intro index inside same
  have original : logical[index]? = some logical[index] := List.getElem?_eq_getElem inside
  have moved := layout.lookup index _ original
  rw [same, found] at moved
  have empty : logical[index] = .tuple [] :=
    (relocateObject_emptyTuple (rename := rename) _).mp (Option.some.inj moved).symm
  exact emptyTupleAddress_absent absent index (by simpa [empty] using original)

private theorem closed_append_tuple (closed : Closed logical) (items : List Value)
    (inside : ∀ value ∈ items, value.edge.Within logical.length) :
    Closed (logical ++ [.tuple items]) := by
  intro object member value valueMember
  have old : value.edge.Within logical.length := by
    rcases List.mem_append.mp member with member | member
    · exact closed object member value valueMember
    · have same := List.mem_singleton.mp member
      subst object
      exact inside value valueMember
  cases value with
  | scalar value => trivial
  | ref address =>
    change address < logical.length at old
    change address < (logical ++ [Object.tuple items]).length
    simp
    omega

/-- The actual tuple allocator agrees under relocation, whether it allocates or interns.
The resulting map still agrees on every pre-existing logical address. -/
theorem RuntimeLayout.allocateTuple (layout : RuntimeLayout logical physical rename)
    (closed : Closed logical) (interned : EmptyTuplesAligned logical physical rename)
    (items : List Value) (inside : ∀ value ∈ items, value.edge.Within logical.length) :
    ∃ left right leftAfter rightAfter nextMap,
      Mutable.allocateTuple items logical = some (.ok (.ref left), leftAfter) ∧
      Mutable.allocateTuple (items.map (relocateValue rename)) physical =
        some (.ok (.ref right), rightAfter) ∧
      RuntimeLayout leftAfter rightAfter nextMap ∧
      EmptyTuplesAligned leftAfter rightAfter nextMap ∧
      Closed leftAfter ∧ left < leftAfter.length ∧ nextMap left = right ∧
      (∀ index < logical.length, nextMap index = rename index) := by
  cases items with
  | nil =>
    cases leftFound : emptyTupleAddress logical with
    | some address =>
      have rightFound := interned address leftFound
      have inside := (List.getElem?_eq_some_iff.mp (emptyTupleAddress_lookup leftFound)).1
      refine ⟨address, rename address, logical, physical, rename, ?_, ?_,
        layout, interned, closed, inside, rfl, fun _ _ => rfl⟩
      · simp only [emptyTupleAddress] at leftFound
        simp [Mutable.allocateTuple, leftFound]
      · simp only [emptyTupleAddress] at rightFound
        simp [Mutable.allocateTuple, rightFound]
    | none =>
      cases rightFound : emptyTupleAddress physical with
      | some address =>
        have found := emptyTupleAddress_lookup rightFound
        have reused := layout.reuse_private closed (.tuple []) address
          (layout.private_emptyTuple leftFound address found) found
        refine ⟨logical.length, address, logical ++ [.tuple []], physical,
          extendMap rename logical.length address, ?_, ?_, reused, ?_,
          closed_append_tuple closed [] inside, by simp, by simp,
          fun i hi => extendMap_old _ _ _ _ hi⟩
        · simp only [emptyTupleAddress] at leftFound
          simp [Mutable.allocateTuple, leftFound]
          rfl
        · simp [Mutable.allocateTuple, emptyTupleAddress] at rightFound ⊢
          simp [rightFound]
        · intro index selected
          have equal : index = logical.length := by
            simp only [emptyTupleAddress] at leftFound selected
            simpa [List.findIdx?_append, leftFound] using selected.symm
          simpa [equal] using rightFound
      | none =>
        refine ⟨logical.length, physical.length, logical ++ [.tuple []], physical ++ [.tuple []],
          extendMap rename logical.length physical.length, ?_, ?_, layout.allocate closed (.tuple []),
          ?_, closed_append_tuple closed [] inside, by simp, by simp,
          fun i hi => extendMap_old _ _ _ _ hi⟩
        · simp only [emptyTupleAddress] at leftFound
          simp [Mutable.allocateTuple, leftFound]
          rfl
        · simp only [emptyTupleAddress] at rightFound
          simp [Mutable.allocateTuple, rightFound]
          rfl
        · intro index selected
          have equal : index = logical.length := by
            simp only [emptyTupleAddress] at leftFound selected
            simpa [List.findIdx?_append, leftFound] using selected.symm
          simp only [emptyTupleAddress] at rightFound ⊢
          simp [List.findIdx?_append, rightFound, equal]
  | cons item items =>
    let object := Object.tuple (item :: items)
    let nextMap := extendMap rename logical.length physical.length
    have same : relocateObject nextMap object = relocateObject rename object :=
      relocateObject_congr _ _ logical.length object
        (fun index bound => extendMap_old _ _ _ _ bound) inside
    have allocated := layout.allocate closed object
    change RuntimeLayout (logical ++ [object]) (physical ++ [relocateObject nextMap object]) nextMap
      at allocated
    rw [same] at allocated
    refine ⟨logical.length, physical.length, logical ++ [object],
      physical ++ [relocateObject rename object], nextMap, rfl, rfl, allocated, ?_,
      closed_append_tuple closed (item :: items) inside, by simp, by simp [nextMap],
      fun i hi => extendMap_old _ _ _ _ hi⟩
    intro index selected
    have old : emptyTupleAddress logical = some index := by
      simpa [emptyTupleAddress, List.findIdx?_append, object] using selected
    have right := interned index old
    have indexBound := (List.getElem?_eq_some_iff.mp (emptyTupleAddress_lookup old)).1
    simpa [emptyTupleAddress, List.findIdx?_append, object, relocateObject, nextMap,
      extendMap_old _ _ _ _ indexBound] using right

end FormalSW.PyAst.Mutable.Relocation

namespace FormalSW.PyAst.HeapCalls.Evaluates

/-- Tuple displays use the actual allocator, including its empty-tuple reuse branch. -/
theorem tuple_result {module : Module} {env : Env} {expressions : List Expr}
    {heap middle after : Heap} {values : List Value} {value : Value}
    {globals : Mutable.Globals}
    (arguments : Arguments (globals := globals) module env expressions heap values middle)
    (allocated : Mutable.allocateTuple values middle = some (.ok value, after)) :
    Evaluates (globals := globals) module env (.tuple expressions) heap value after := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments .tuple [] anchors stack).trans
  apply Reaches.next (following := ⟨.value value, stack, after⟩) ?_ .refl
  have operation : primitive .tuple values middle = some (.ok value, after) := allocated
  simp [step, result, run, operation]

end FormalSW.PyAst.HeapCalls.Evaluates
