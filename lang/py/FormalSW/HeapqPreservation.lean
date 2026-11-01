import lang.py.FormalSW.HeapqCalls

/-! Heap sifts only exchange list entries. Preservation includes exception exits,
which retain the swaps already performed. Unsupported comparisons have no modeled
outcome; these theorems do not assert that such comparisons are supported. -/
namespace FormalSW.PyAst.Heapq

attribute [local simp] Except.map

/-- A heap predicate holds after every modeled success or exception. -/
def Preserves (invariant : Heap → Prop) (action : Eval α) : Prop :=
  ∀ heap outcome after, invariant heap → action heap = some (outcome, after) → invariant after

theorem Preserves.pure (invariant : Heap → Prop) (value : α) :
    Preserves invariant (pure value) := by
  intro heap outcome after holds finished
  have same : heap = after := by simpa using congrArg (Option.map Prod.snd) finished
  exact same ▸ holds

theorem Preserves.error (invariant : Heap → Prop) (name : String) :
    Preserves invariant (Mutable.error (α := α) name) := by
  intro heap outcome after holds finished
  have same : heap = after := by simpa [Mutable.error] using congrArg (Option.map Prod.snd) finished
  exact same ▸ holds

theorem Preserves.bind (first : Eval α) (next : α → Eval β) (invariant : Heap → Prop)
    (firstPreserves : Preserves invariant first)
    (nextPreserves : ∀ value, Preserves invariant (next value)) :
    Preserves invariant (first >>= next) := by
  intro heap outcome after holds finished
  rw [Mutable.eval_bind] at finished
  cases ran : first heap with
  | none => simp [ran] at finished
  | some result =>
      obtain ⟨result, middle⟩ := result
      have preserved := firstPreserves heap result middle holds ran
      cases result with
      | error exception =>
          simp [ran] at finished
          exact finished.2 ▸ preserved
      | ok value =>
          exact nextPreserves value middle outcome after preserved (by simpa [ran] using finished)

theorem Preserves.map (first : Eval α) (convert : α → β) (invariant : Heap → Prop)
    (preserved : Preserves invariant first) : Preserves invariant (convert <$> first) := by
  intro heap outcome after holds finished
  rw [Mutable.eval_map] at finished
  cases ran : first heap with
  | none => simp [ran] at finished
  | some result =>
      obtain ⟨result, middle⟩ := result
      have kept := preserved heap result middle holds ran
      simp [ran] at finished
      exact finished.2 ▸ kept

theorem preserves_items (invariant : Heap → Prop) (address : Nat) :
    Preserves invariant (items address) := by
  intro heap outcome after holds finished
  cases found : heap[address]? with
  | none => simp [items, found, Mutable.unsupported] at finished
  | some object => cases object <;> simp_all [items, Mutable.error]

theorem preserves_atIndex (invariant : Heap → Prop) (address position : Nat) :
    Preserves invariant (atIndex address position) := by
  apply Preserves.bind _ _ _ (preserves_items invariant address)
  intro values
  cases values[position]? with
  | none => exact Preserves.error invariant "IndexError"
  | some value => exact Preserves.pure invariant value

theorem preserves_receiver (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (receiver value) := by
  cases value with
  | scalar _ => exact Preserves.error invariant "TypeError"
  | ref address =>
      exact Preserves.bind _ _ _ (preserves_items invariant address)
        (fun _ => Preserves.pure invariant address)

theorem preserves_less (invariant : Heap → Prop) (left right : Value) :
    Preserves invariant (less left right) := by
  intro heap outcome after holds finished
  cases compared : HeapSort.compare (heap.length + 1) heap false left right with
  | none => simp [less, compared, Mutable.unsupported] at finished
  | some result => cases result <;> simp_all [less]

/-- Swaps at the designated list preserve the predicate, including shared references. -/
def SwapInvariant (address : Nat) (invariant : Heap → Prop) : Prop :=
  ∀ heap values left right (hl : left < values.length) (hr : right < values.length),
    invariant heap → heap[address]? = some (.list values) →
      invariant (heap.set address (.list ((values.set left values[right]).set right values[left])))

theorem preserves_swap (address left right : Nat) (invariant : Heap → Prop)
    (stable : SwapInvariant address invariant) :
    Preserves invariant (swap address left right) := by
  intro heap outcome after holds finished
  cases found : heap[address]? with
  | none => simp [swap, items, found, Mutable.unsupported] at finished
  | some object =>
      cases object <;> try
        (simp [swap, items, found, Mutable.error] at finished; exact finished.2 ▸ holds)
      case list values =>
        by_cases hl : left < values.length
        · by_cases hr : right < values.length
          · rw [swap_list heap address left right values found hl hr] at finished
            have same := congrArg Prod.snd (Option.some.inj finished)
            dsimp only at same
            exact same ▸ stable heap values left right hl hr holds found
          · simp [swap, items_list heap address values found,
              List.getElem?_eq_none (Nat.le_of_not_gt hr), Mutable.error] at finished
            exact finished.2 ▸ holds
        · simp [swap, items_list heap address values found,
            List.getElem?_eq_none (Nat.le_of_not_gt hl), Mutable.error] at finished
          exact finished.2 ▸ holds

theorem preserves_siftDown (address start position : Nat) (invariant : Heap → Prop)
    (stable : SwapInvariant address invariant) :
    Preserves invariant (siftDown address start position) := by
  rw [siftDown]
  split
  · rename_i moving
    apply Preserves.bind _ _ _ (preserves_atIndex invariant address position)
    intro value
    apply Preserves.bind _ _ _ (preserves_atIndex invariant address ((position - 1) / 2))
    intro above
    apply Preserves.bind _ _ _ (preserves_less invariant value above)
    intro smaller
    cases smaller with
    | false => exact Preserves.pure invariant ()
    | true =>
        exact Preserves.bind _ _ _ (preserves_swap address position ((position - 1) / 2)
          invariant stable) (fun _ => preserves_siftDown address start ((position - 1) / 2)
            invariant stable)
  · exact Preserves.pure invariant ()
termination_by position
decreasing_by
  have := Nat.div_le_self (position - 1) 2
  omega

theorem preserves_siftChildren (address size start position : Nat) (invariant : Heap → Prop)
    (stable : SwapInvariant address invariant) :
    Preserves invariant (siftChildren address size start position) := by
  rw [siftChildren]
  split
  · dsimp only
    split
    · apply Preserves.bind _ _ _ (preserves_atIndex invariant address (2 * position + 1))
      intro left
      apply Preserves.bind _ _ _ (preserves_atIndex invariant address (2 * position + 1 + 1))
      intro right
      apply Preserves.bind _ _ _ (preserves_less invariant left right)
      intro smaller
      cases smaller with
      | false =>
          exact Preserves.bind _ _ _ (preserves_swap address position (2 * position + 1 + 1)
            invariant stable) (fun _ => preserves_siftChildren address size start
              (2 * position + 1 + 1) invariant stable)
      | true =>
          exact Preserves.bind _ _ _ (preserves_swap address position (2 * position + 1)
            invariant stable) (fun _ => preserves_siftChildren address size start
              (2 * position + 1) invariant stable)
    · exact Preserves.bind _ _ _ (preserves_swap address position (2 * position + 1)
        invariant stable) (fun _ => preserves_siftChildren address size start
          (2 * position + 1) invariant stable)
  · exact preserves_siftDown address start position invariant stable
termination_by size - position
decreasing_by all_goals omega

theorem preserves_siftUp (address position : Nat) (invariant : Heap → Prop)
    (stable : SwapInvariant address invariant) :
    Preserves invariant (siftUp address position) := by
  apply Preserves.bind _ _ _ (preserves_items invariant address)
  intro values
  split
  · exact preserves_siftChildren address values.length position position invariant stable
  · exact Preserves.error invariant "IndexError"

theorem preserves_siftAll (address : Nat) (positions : List Nat) (invariant : Heap → Prop)
    (stable : SwapInvariant address invariant) :
    Preserves invariant (siftAll address positions) := by
  induction positions with
  | nil => exact Preserves.pure invariant ()
  | cons position rest ih =>
      exact Preserves.bind _ _ _ (preserves_siftUp address position invariant stable) (fun _ => ih)

/-- Both heapify traversal strategies preserve every swap invariant. -/
theorem preserves_heapify (address : Nat) (invariant : Heap → Prop)
    (stable : SwapInvariant address invariant) :
    Preserves invariant (heapify [.ref address]) := by
  intro heap outcome after holds finished
  cases found : heap[address]? with
  | none => simp [heapify, receiver, items, found, Mutable.unsupported] at finished
  | some object =>
      cases object <;> try
        (simp [heapify, receiver, items, found, Mutable.error] at finished
         exact finished.2 ▸ holds)
      case list values =>
        have preservation := Preserves.map _ (fun _ => (.scalar .none : Value)) invariant
          (preserves_siftAll address (heapifyOrder values.length) invariant stable)
        apply preservation heap outcome after holds
        simpa [heapify, receiver_list heap address values found,
          items_list heap address values found] using finished

end FormalSW.PyAst.Heapq
