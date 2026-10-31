import lang.py.FormalSW.HeapqContents

/-! Heap operations terminate when comparisons succeed under an invariant that
is preserved by replacing the queue list. Referenced tuple objects may therefore
supply comparison keys without requiring them to exist in unrelated heaps. -/
namespace FormalSW.PyAst.Heapq

attribute [local simp] Except.map

def ComparisonUnder (invariant : Heap → Prop) (domain : Value → Prop) : Prop :=
  ∀ heap, invariant heap → ∀ left right, domain left → domain right →
    ∃ answer, less left right heap = some (.ok answer, heap)

def ListReplacementInvariant (address : Nat) (invariant : Heap → Prop) : Prop :=
  ∀ heap values, invariant heap → invariant (heap.set address (.list values))

theorem ListReplacementInvariant.reorders {address : Nat} {invariant : Heap → Prop}
    (stable : ListReplacementInvariant address invariant) {heap after : Heap} {values : List Value}
    (kept : invariant heap) (reordered : Reorders heap address values after) : invariant after := by
  obtain ⟨changed, _, rfl⟩ := reordered
  exact stable heap changed kept

theorem siftDown_succeeds_under (domain : Value → Prop) (invariant : Heap → Prop) (comparable : ComparisonUnder invariant domain)
    (heap : Heap) (address start position : Nat) (values : List Value)
    (stable : ListReplacementInvariant address invariant) (kept : invariant heap)
    (typed : ∀ value ∈ values, domain value) (found : heap[address]? = some (.list values))
    (inside : position < values.length) :
    ∃ after, siftDown address start position heap = some (.ok (), after) := by
  by_cases moving : start < position
  · let parent := (position - 1) / 2
    have smaller : parent < position := by
      have := Nat.div_le_self (position - 1) 2
      dsimp [parent]
      omega
    have parentInside : parent < values.length := Nat.lt_trans smaller inside
    obtain ⟨answer, compared⟩ := comparable heap kept values[position] values[parent]
      (typed _ (List.getElem_mem inside)) (typed _ (List.getElem_mem parentInside))
    cases answer with
    | false =>
        refine ⟨heap, ?_⟩
        rw [siftDown]
        simp [moving, atIndex_list heap address position values found inside,
          atIndex_list heap address parent values found parentInside, compared, parent]
    | true =>
        let changed := (values.set position values[parent]).set parent values[position]
        have permutation : changed.Perm values := swap_contents_perm values position parent inside
          parentInside
        have valid := (List.getElem?_eq_some_iff.mp found).1
        have changedFound :
            (heap.set address (.list changed))[address]? = some (.list changed) := by
          simp [valid]
        obtain ⟨after, finished⟩ := siftDown_succeeds_under domain invariant comparable
          (heap.set address (.list changed)) address start parent changed stable (stable heap changed kept)
          (fun value member => typed value (permutation.mem_iff.mp member)) changedFound
          (by rw [permutation.length_eq]; exact parentInside)
        refine ⟨after, ?_⟩
        rw [siftDown]
        simp [moving, atIndex_list heap address position values found inside,
          atIndex_list heap address parent values found parentInside, compared,
          swap_list heap address position parent values found inside parentInside,
          finished, parent, changed]
  · exact ⟨heap, siftDown_stop heap address start position (Nat.le_of_not_gt moving)⟩
termination_by position
decreasing_by exact smaller

theorem siftChildren_succeeds_under (domain : Value → Prop) (invariant : Heap → Prop) (comparable : ComparisonUnder invariant domain)
    (heap : Heap) (address size start position : Nat) (values : List Value)
    (stable : ListReplacementInvariant address invariant) (kept : invariant heap)
    (typed : ∀ value ∈ values, domain value) (found : heap[address]? = some (.list values))
    (sized : size ≤ values.length) (inside : position < size) :
    ∃ after, siftChildren address size start position heap = some (.ok (), after) := by
  have descend (child : Nat) (childInside : child < size) (progress : position < child) :
      ∃ after, (do swap address position child
                   siftChildren address size start child) heap = some (.ok (), after) := by
    have positionValid := Nat.lt_of_lt_of_le inside sized
    have childValid := Nat.lt_of_lt_of_le childInside sized
    let changed := (values.set position values[child]).set child values[position]
    have permutation : changed.Perm values :=
      swap_contents_perm values position child positionValid childValid
    have valid := (List.getElem?_eq_some_iff.mp found).1
    have changedFound : (heap.set address (.list changed))[address]? = some (.list changed) := by
      simp [valid]
    obtain ⟨after, finished⟩ := siftChildren_succeeds_under domain invariant comparable
      (heap.set address (.list changed)) address size start child changed stable (stable heap changed kept)
      (fun value member => typed value (permutation.mem_iff.mp member)) changedFound
      (by rw [permutation.length_eq]; exact sized) childInside
    exact ⟨after, by
      simp [swap_list heap address position child values found positionValid childValid,
        changed, finished]⟩
  by_cases leftInside : 2 * position + 1 < size
  · by_cases rightInside : 2 * position + 1 + 1 < size
    · have leftValid := Nat.lt_of_lt_of_le leftInside sized
      have rightValid := Nat.lt_of_lt_of_le rightInside sized
      obtain ⟨answer, compared⟩ := comparable heap kept values[2 * position + 1]
        values[2 * position + 1 + 1] (typed _ (List.getElem_mem leftValid))
        (typed _ (List.getElem_mem rightValid))
      cases answer with
      | false =>
          obtain ⟨after, finished⟩ := descend (2 * position + 1 + 1) rightInside (by omega)
          refine ⟨after, ?_⟩
          rw [siftChildren]
          simpa [leftInside, rightInside,
            atIndex_list heap address (2 * position + 1) values found leftValid,
            atIndex_list heap address (2 * position + 1 + 1) values found rightValid,
            compared] using finished
      | true =>
          obtain ⟨after, finished⟩ := descend (2 * position + 1) leftInside (by omega)
          refine ⟨after, ?_⟩
          rw [siftChildren]
          simpa [leftInside, rightInside,
            atIndex_list heap address (2 * position + 1) values found leftValid,
            atIndex_list heap address (2 * position + 1 + 1) values found rightValid,
            compared] using finished
    · obtain ⟨after, finished⟩ := descend (2 * position + 1) leftInside (by omega)
      refine ⟨after, ?_⟩
      rw [siftChildren]
      simpa [leftInside, rightInside] using finished
  · obtain ⟨after, finished⟩ := siftDown_succeeds_under domain invariant comparable heap
      address start position values stable kept typed found (Nat.lt_of_lt_of_le inside sized)
    refine ⟨after, ?_⟩
    rw [siftChildren]
    simpa [leftInside] using finished
termination_by size - position
decreasing_by omega

theorem siftUp_succeeds_under (domain : Value → Prop) (invariant : Heap → Prop) (comparable : ComparisonUnder invariant domain)
    (heap : Heap) (address position : Nat) (values : List Value)
    (stable : ListReplacementInvariant address invariant) (kept : invariant heap)
    (typed : ∀ value ∈ values, domain value) (found : heap[address]? = some (.list values))
    (inside : position < values.length) :
    ∃ after, siftUp address position heap = some (.ok (), after) := by
  obtain ⟨after, finished⟩ := siftChildren_succeeds_under domain invariant comparable heap address values.length
    position position values stable kept typed found (Nat.le_refl _) inside
  exact ⟨after, by simp [siftUp, items_list heap address values found, inside, finished]⟩

theorem siftAll_succeeds_under (domain : Value → Prop) (invariant : Heap → Prop) (comparable : ComparisonUnder invariant domain)
    (heap : Heap) (address : Nat) (values : List Value) (positions : List Nat)
    (stable : ListReplacementInvariant address invariant) (kept : invariant heap)
    (typed : ∀ value ∈ values, domain value) (found : heap[address]? = some (.list values))
    (inside : ∀ position ∈ positions, position < values.length) :
    ∃ after, siftAll address positions heap = some (.ok (), after) := by
  induction positions generalizing heap values with
  | nil => exact ⟨heap, rfl⟩
  | cons position rest ih =>
      obtain ⟨middle, first⟩ := siftUp_succeeds_under domain invariant comparable heap address position values stable kept typed
        found (inside position (by simp))
      obtain ⟨changed, changedFound, permutation⟩ := Reorders.contents heap address values middle
        (List.getElem?_eq_some_iff.mp found).1
        (siftUp_reorders heap middle address position values (.ok ()) found first)
      have middleKept : invariant middle := stable.reorders kept
        (siftUp_reorders heap middle address position values (.ok ()) found first)
      obtain ⟨after, finished⟩ := ih middle changed middleKept
        (fun value member => typed value (permutation.mem_iff.mp member)) changedFound
        (fun index member => by rw [permutation.length_eq]; exact inside index (by simp [member]))
      exact ⟨after, by simp [siftAll, first, finished]⟩

theorem mem_parentPath_le (position index : Nat) (member : index ∈ parentPath position) :
    index ≤ position := by
  rw [parentPath] at member
  rcases List.mem_cons.mp member with same | tail
  · omega
  · by_cases odd : position % 2 = 1
    · rw [if_pos odd] at tail
      exact Nat.le_trans (mem_parentPath_le (position / 2) index tail)
        (Nat.div_le_self position 2)
    · simp [odd] at tail
termination_by position
decreasing_by apply Nat.div_lt_self <;> omega

theorem mem_descending_bounds (start count index : Nat) (member : index ∈ descending start count) :
    start ≤ index ∧ index < start + count := by
  simp only [descending, List.mem_map, List.mem_reverse, List.mem_range] at member
  obtain ⟨offset, smaller, rfl⟩ := member
  omega

/-- Both cache strategies visit only actual internal nodes of the list. -/
theorem heapifyOrder_internal (size position : Nat) (member : position ∈ heapifyOrder size) :
    position < size / 2 := by
  by_cases cached : size > 2500
  · rw [heapifyOrder, if_pos cached] at member
    dsimp only at member
    obtain ⟨ancestor, visited, path⟩ := List.mem_flatMap.mp member
    have below := mem_parentPath_le ancestor position path
    have leftBound : 2 ^ Nat.log2 (size / 2 + 1) - 1 ≤ size / 2 := by
      have : 2 ^ Nat.log2 (size / 2 + 1) ≤ size / 2 + 1 :=
        Nat.log2_self_le (by omega)
      omega
    have halfBound := Nat.div_le_self (size / 2) 2
    rcases List.mem_append.mp visited with left | right
    · have bounds := mem_descending_bounds _ _ _ left
      omega
    · have bounds := mem_descending_bounds _ _ _ right
      omega
  · simpa [heapifyOrder, cached] using member

theorem heapifyOrder_valid (size position : Nat) (member : position ∈ heapifyOrder size) :
    position < size := by
  have := heapifyOrder_internal size position member
  have := Nat.div_le_self size 2
  omega

theorem heapify_succeeds_under (domain : Value → Prop) (invariant : Heap → Prop) (comparable : ComparisonUnder invariant domain)
    (heap : Heap) (address : Nat) (values : List Value)
    (stable : ListReplacementInvariant address invariant) (kept : invariant heap)
    (typed : ∀ value ∈ values, domain value) (found : heap[address]? = some (.list values)) :
    ∃ after, heapify [.ref address] heap = some (.ok (.scalar .none), after) := by
  obtain ⟨after, finished⟩ := siftAll_succeeds_under domain invariant comparable heap address values
    (heapifyOrder values.length) stable kept typed found (heapifyOrder_valid values.length)
  exact ⟨after, heapify_result heap after address values (.ok ()) found finished⟩

theorem heappush_succeeds_under (domain : Value → Prop) (invariant : Heap → Prop) (comparable : ComparisonUnder invariant domain)
    (heap : Heap) (address : Nat) (values : List Value) (item : Value)
    (stable : ListReplacementInvariant address invariant) (kept : invariant heap)
    (typed : ∀ value ∈ values, domain value) (itemTyped : domain item)
    (found : heap[address]? = some (.list values)) :
    ∃ after, heappush [.ref address, item] heap = some (.ok (.scalar .none), after) := by
  have valid := (List.getElem?_eq_some_iff.mp found).1
  have appended : ∀ value ∈ values ++ [item], domain value := by
    intro value member
    rcases List.mem_append.mp member with old | new
    · exact typed value old
    · simpa using (List.mem_singleton.mp new) ▸ itemTyped
  obtain ⟨after, finished⟩ := siftDown_succeeds_under domain invariant comparable
    (heap.set address (.list (values ++ [item]))) address 0 values.length (values ++ [item])
    stable (stable heap _ kept) appended (by simp [valid]) (by simp)
  exact ⟨after, heappush_result heap after address values item (.ok ()) found finished⟩

theorem heappop_succeeds_under (domain : Value → Prop) (invariant : Heap → Prop) (comparable : ComparisonUnder invariant domain)
    (heap : Heap) (address : Nat) (root : Value) (rest : List Value)
    (stable : ListReplacementInvariant address invariant) (kept : invariant heap)
    (typed : ∀ value ∈ root :: rest, domain value)
    (found : heap[address]? = some (.list (root :: rest))) :
    ∃ after, heappop [.ref address] heap = some (.ok root, after) := by
  rcases List.eq_nil_or_concat rest with empty | ⟨middle, last, equation⟩
  · subst rest
    exact ⟨_, heappop_singleton heap address root found⟩
  · have tail : rest = middle ++ [last] := by simpa only [List.concat_eq_append] using equation
    clear equation
    subst rest
    have valid := (List.getElem?_eq_some_iff.mp found).1
    have permutation : (last :: middle).Perm (middle ++ [last]) :=
      List.perm_append_comm (l₁ := [last]) (l₂ := middle)
    obtain ⟨after, finished⟩ := siftUp_succeeds_under domain invariant comparable
      (heap.set address (.list (last :: middle))) address 0 (last :: middle)
      stable (stable heap _ kept) (fun value member => typed value (List.mem_cons_of_mem root (permutation.mem_iff.mp member)))
      (by simp [valid]) (by simp)
    refine ⟨after, ?_⟩
    rw [heappop_nontrivial heap address root last middle found]
    simp [finished]

end FormalSW.PyAst.Heapq
