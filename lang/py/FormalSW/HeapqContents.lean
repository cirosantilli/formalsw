import lang.py.FormalSW.HeapqPreservation

/-! Contents and exact caller-heap frames for the concrete heap operations.
Theorems retain actual value references and their multiplicities. -/
namespace FormalSW.PyAst.Heapq

attribute [local simp] Except.map

private theorem cons_set_perm (values : List α) (position : Nat)
    (valid : position < values.length) (value : α) :
    (values[position] :: values.set position value).Perm (value :: values) := by
  induction values generalizing position with
  | nil => simp at valid
  | cons first rest ih =>
      cases position with
      | zero => exact .swap _ _ _
      | succ position =>
          have inside : position < rest.length := by simpa using valid
          exact (List.Perm.swap _ _ _).trans
            (((ih position inside).cons first).trans (List.Perm.swap _ _ _))

theorem swap_contents_perm (values : List α) (left right : Nat)
    (hl : left < values.length) (hr : right < values.length) :
    ((values.set left values[right]).set right values[left]).Perm values := by
  induction values generalizing left right with
  | nil => simp at hl
  | cons first rest ih =>
      cases left with
      | zero =>
          cases right with
          | zero => exact .refl _
          | succ right => exact cons_set_perm rest right (by simpa using hr) first
      | succ left =>
          cases right with
          | zero => exact cons_set_perm rest left (by simpa using hl) first
          | succ right => exact (ih left right (by simpa using hl) (by simpa using hr)).cons first

/-- Exchange encoded entries without changing their representation or caller heap frame. -/
theorem swap_mapped_list (encode : α → Value) (heap : Heap) (address left right : Nat)
    (values : List α) (found : heap[address]? = some (.list (values.map encode)))
    (hl : left < values.length) (hr : right < values.length) :
    swap address left right heap = some (.ok (), heap.set address
      (.list (((values.set left values[right]).set right values[left]).map encode))) := by
  have leftEq : (values.map encode)[left]'(by simpa using hl) = encode values[left] :=
    List.getElem_map encode
  have rightEq : (values.map encode)[right]'(by simpa using hr) = encode values[right] :=
    List.getElem_map encode
  have result := swap_list heap address left right (values.map encode) found
    (by simpa using hl) (by simpa using hr)
  rw [leftEq, rightEq] at result
  simpa only [List.map_set] using result

/-- Only the designated list changes; its contents are a permutation of the supplied values. -/
def Reorders (original : Heap) (address : Nat) (values : List Value) (after : Heap) : Prop :=
  ∃ changed, changed.Perm values ∧ after = original.set address (.list changed)

theorem Reorders.refl (heap : Heap) (address : Nat) (values : List Value)
    (found : heap[address]? = some (.list values)) : Reorders heap address values heap := by
  obtain ⟨valid, entry⟩ := List.getElem?_eq_some_iff.mp found
  refine ⟨values, .refl _, ?_⟩
  rw [← entry, List.set_getElem_self valid]

theorem Reorders.swapInvariant (original : Heap) (address : Nat) (values : List Value)
    (valid : address < original.length) :
    SwapInvariant address (Reorders original address values) := by
  intro heap current left right hl hr reordered found
  obtain ⟨changed, permutation, rfl⟩ := reordered
  have same : changed = current := by simpa [valid] using found
  subst current
  refine ⟨_, (swap_contents_perm changed left right hl hr).trans permutation, ?_⟩
  simp

theorem Reorders.contents (original : Heap) (address : Nat) (values : List Value) (after : Heap)
    (valid : address < original.length) (reordered : Reorders original address values after) :
    ∃ changed, after[address]? = some (.list changed) ∧ changed.Perm values := by
  obtain ⟨changed, permutation, rfl⟩ := reordered
  exact ⟨changed, by simp [valid], permutation⟩

theorem Reorders.frame (original : Heap) (address : Nat) (values : List Value) (after : Heap)
    (reordered : Reorders original address values after) :
    after.length = original.length ∧
      ∀ other, other ≠ address → after[other]? = original[other]? := by
  obtain ⟨changed, _, rfl⟩ := reordered
  exact ⟨by simp, fun other different => by simp [Ne.symm different]⟩

theorem siftDown_reorders (heap after : Heap) (address start position : Nat) (values : List Value)
    (outcome : Except ExceptionObject Unit) (found : heap[address]? = some (.list values))
    (finished : siftDown address start position heap = some (outcome, after)) :
    Reorders heap address values after :=
  preserves_siftDown address start position _
    (Reorders.swapInvariant heap address values (List.getElem?_eq_some_iff.mp found).1)
    heap outcome after (Reorders.refl heap address values found) finished

theorem siftChildren_reorders (heap after : Heap) (address size start position : Nat)
    (values : List Value) (outcome : Except ExceptionObject Unit)
    (found : heap[address]? = some (.list values))
    (finished : siftChildren address size start position heap = some (outcome, after)) :
    Reorders heap address values after :=
  preserves_siftChildren address size start position _
    (Reorders.swapInvariant heap address values (List.getElem?_eq_some_iff.mp found).1)
    heap outcome after (Reorders.refl heap address values found) finished

theorem siftUp_reorders (heap after : Heap) (address position : Nat) (values : List Value)
    (outcome : Except ExceptionObject Unit) (found : heap[address]? = some (.list values))
    (finished : siftUp address position heap = some (outcome, after)) :
    Reorders heap address values after :=
  preserves_siftUp address position _
    (Reorders.swapInvariant heap address values (List.getElem?_eq_some_iff.mp found).1)
    heap outcome after (Reorders.refl heap address values found) finished

theorem heapify_reorders (heap after : Heap) (address : Nat) (values : List Value)
    (outcome : Except ExceptionObject Value) (found : heap[address]? = some (.list values))
    (finished : heapify [.ref address] heap = some (outcome, after)) :
    Reorders heap address values after :=
  preserves_heapify address _
    (Reorders.swapInvariant heap address values (List.getElem?_eq_some_iff.mp found).1)
    heap outcome after (Reorders.refl heap address values found) finished

/-- An appended item remains present even if a later comparison raises an exception. -/
theorem heappush_reorders (heap after : Heap) (address : Nat) (values : List Value) (item : Value)
    (outcome : Except ExceptionObject Value) (found : heap[address]? = some (.list values))
    (finished : heappush [.ref address, item] heap = some (outcome, after)) :
    Reorders heap address (values ++ [item]) after := by
  have preservation := Preserves.map _ (fun _ => (.scalar .none : Value)) _
    (preserves_siftDown address 0 values.length _
      (Reorders.swapInvariant heap address (values ++ [item])
        (List.getElem?_eq_some_iff.mp found).1))
  apply preservation (heap.set address (.list (values ++ [item]))) outcome after
    ⟨values ++ [item], .refl _, rfl⟩
  simpa [heappush, receiver_list heap address values found,
    items_list heap address values found, Mutable.appendItem, found] using finished

private theorem pop_last (values : List Value) (last : Value) :
    Py.Builtin.List.pop (values ++ [last]) (-1) = .ok (last, values) := by
  have shifted : (-1 : Int) + ((values.length + 1 : Nat) : Int) = values.length := by omega
  have normalized : Py.Builtin.Sequence.normalizeIndex (values.length + 1) (-1) =
      some values.length := by
    unfold Py.Builtin.Sequence.normalizeIndex
    dsimp only
    rw [shifted]
    simp
    omega
  simp [Py.Builtin.List.pop, normalized, bind, pure, Except.bind, Except.pure]

theorem popItem_last (heap : Heap) (address : Nat) (values : List Value) (last : Value)
    (found : heap[address]? = some (.list (values ++ [last]))) :
    Mutable.popItem address (.scalar (.int (-1))) heap =
      some (.ok last, heap.set address (.list values)) := by
  simp only [Mutable.popItem, Mutable.integer, Mutable.eval_bind, Mutable.eval_pure,
    Mutable.eval_get, Option.bind_eq_bind, Option.bind_some, found, pop_last]
  rfl

/-- Replace the root by the last element before sifting; the returned value is the old root. -/
theorem heappop_nontrivial (heap : Heap) (address : Nat) (root last : Value) (middle : List Value)
    (found : heap[address]? = some (.list (root :: (middle ++ [last])))) :
    heappop [.ref address] heap =
      ((fun _ => root) <$> siftUp address 0) (heap.set address (.list (last :: middle))) := by
  have valid := (List.getElem?_eq_some_iff.mp found).1
  have popped := popItem_last heap address (root :: middle) last found
  simp [heappop, receiver_list heap address (root :: (middle ++ [last])) found,
    popped, items, valid]

/-- Pop removes the old root even if a comparison in the subsequent sift fails. -/
theorem heappop_reorders (heap after : Heap) (address : Nat) (root : Value) (rest : List Value)
    (outcome : Except ExceptionObject Value) (found : heap[address]? = some (.list (root :: rest)))
    (finished : heappop [.ref address] heap = some (outcome, after)) :
    Reorders heap address rest after := by
  have valid := (List.getElem?_eq_some_iff.mp found).1
  rcases List.eq_nil_or_concat rest with empty | ⟨middle, last, equation⟩
  · subst rest
    rw [heappop_singleton heap address root found] at finished
    have same := congrArg Prod.snd (Option.some.inj finished)
    exact ⟨[], .refl _, same.symm⟩
  · have tail : rest = middle ++ [last] := by simpa only [List.concat_eq_append] using equation
    clear equation
    subst rest
    have preservation := Preserves.map _ (fun _ => root) _
      (preserves_siftUp address 0 _ (Reorders.swapInvariant heap address (middle ++ [last]) valid))
    apply preservation (heap.set address (.list (last :: middle))) outcome after
      ⟨last :: middle, List.perm_append_comm (l₁ := [last]) (l₂ := middle), rfl⟩
    exact (heappop_nontrivial heap address root last middle found) ▸ finished

theorem heappop_returns_root (heap after : Heap) (address : Nat) (root returned : Value)
    (rest : List Value) (found : heap[address]? = some (.list (root :: rest)))
    (finished : heappop [.ref address] heap = some (.ok returned, after)) : returned = root := by
  rcases List.eq_nil_or_concat rest with empty | ⟨middle, last, equation⟩
  · subst rest
    rw [heappop_singleton heap address root found] at finished
    simpa using (congrArg (Option.map Prod.fst) finished).symm
  · have tail : rest = middle ++ [last] := by simpa only [List.concat_eq_append] using equation
    clear equation
    subst rest
    rw [heappop_nontrivial heap address root last middle found, Mutable.eval_map] at finished
    cases ran : siftUp address 0 (heap.set address (.list (last :: middle))) with
    | none => simp [ran] at finished
    | some result =>
        obtain ⟨result, finalHeap⟩ := result
        cases result <;> simp_all

end FormalSW.PyAst.Heapq
