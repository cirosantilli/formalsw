import lang.py.FormalSW.HeapqFramedTotal

/-! Successful execution of the concrete heap operations on comparison domains.
The domain condition applies at every caller heap; strings and integers satisfy it
without a bound on list length, string length, or integer magnitude. -/
namespace FormalSW.PyAst.Heapq

attribute [local simp] Except.map

def TotalComparison (domain : Value → Prop) : Prop :=
  ∀ heap left right, domain left → domain right →
    ∃ answer, less left right heap = some (.ok answer, heap)

theorem TotalComparison.strings :
    TotalComparison (fun value => ∃ text, value = .scalar (.string text)) := by
  intro heap left right leftTyped rightTyped
  obtain ⟨left, rfl⟩ := leftTyped
  obtain ⟨right, rfl⟩ := rightTyped
  exact ⟨decide (left < right), less_string heap left right⟩

theorem TotalComparison.integers :
    TotalComparison (fun value => ∃ number, value = .scalar (.int number)) := by
  intro heap left right leftTyped rightTyped
  obtain ⟨left, rfl⟩ := leftTyped
  obtain ⟨right, rfl⟩ := rightTyped
  exact ⟨decide (left < right), less_int heap left right⟩

/-- Scalar comparison domains are the invariant-free special case. -/
theorem TotalComparison.under_true {domain : Value → Prop} (comparable : TotalComparison domain) :
    ComparisonUnder (fun _ => True) domain := by
  intro heap _
  exact comparable heap

theorem siftDown_succeeds (domain : Value → Prop) (comparable : TotalComparison domain)
    (heap : Heap) (address start position : Nat) (values : List Value)
    (typed : ∀ value ∈ values, domain value) (found : heap[address]? = some (.list values))
    (inside : position < values.length) :
    ∃ after, siftDown address start position heap = some (.ok (), after) := by
  exact siftDown_succeeds_under domain (fun _ => True) comparable.under_true
    heap address start position values (fun _ _ _ => True.intro) trivial typed found inside

theorem siftChildren_succeeds (domain : Value → Prop) (comparable : TotalComparison domain)
    (heap : Heap) (address size start position : Nat) (values : List Value)
    (typed : ∀ value ∈ values, domain value) (found : heap[address]? = some (.list values))
    (sized : size ≤ values.length) (inside : position < size) :
    ∃ after, siftChildren address size start position heap = some (.ok (), after) := by
  exact siftChildren_succeeds_under domain (fun _ => True) comparable.under_true
    heap address size start position values (fun _ _ _ => True.intro) trivial typed found sized inside

theorem siftUp_succeeds (domain : Value → Prop) (comparable : TotalComparison domain)
    (heap : Heap) (address position : Nat) (values : List Value)
    (typed : ∀ value ∈ values, domain value) (found : heap[address]? = some (.list values))
    (inside : position < values.length) :
    ∃ after, siftUp address position heap = some (.ok (), after) := by
  exact siftUp_succeeds_under domain (fun _ => True) comparable.under_true
    heap address position values (fun _ _ _ => True.intro) trivial typed found inside

theorem siftAll_succeeds (domain : Value → Prop) (comparable : TotalComparison domain)
    (heap : Heap) (address : Nat) (values : List Value) (positions : List Nat)
    (typed : ∀ value ∈ values, domain value) (found : heap[address]? = some (.list values))
    (inside : ∀ position ∈ positions, position < values.length) :
    ∃ after, siftAll address positions heap = some (.ok (), after) := by
  exact siftAll_succeeds_under domain (fun _ => True) comparable.under_true
    heap address values positions (fun _ _ _ => True.intro) trivial typed found inside

theorem heapify_succeeds (domain : Value → Prop) (comparable : TotalComparison domain)
    (heap : Heap) (address : Nat) (values : List Value)
    (typed : ∀ value ∈ values, domain value) (found : heap[address]? = some (.list values)) :
    ∃ after, heapify [.ref address] heap = some (.ok (.scalar .none), after) := by
  exact heapify_succeeds_under domain (fun _ => True) comparable.under_true
    heap address values (fun _ _ _ => True.intro) trivial typed found

theorem heappush_succeeds (domain : Value → Prop) (comparable : TotalComparison domain)
    (heap : Heap) (address : Nat) (values : List Value) (item : Value)
    (typed : ∀ value ∈ values, domain value) (itemTyped : domain item)
    (found : heap[address]? = some (.list values)) :
    ∃ after, heappush [.ref address, item] heap = some (.ok (.scalar .none), after) := by
  exact heappush_succeeds_under domain (fun _ => True) comparable.under_true
    heap address values item (fun _ _ _ => True.intro) trivial typed itemTyped found

theorem heappop_succeeds (domain : Value → Prop) (comparable : TotalComparison domain)
    (heap : Heap) (address : Nat) (root : Value) (rest : List Value)
    (typed : ∀ value ∈ root :: rest, domain value)
    (found : heap[address]? = some (.list (root :: rest))) :
    ∃ after, heappop [.ref address] heap = some (.ok root, after) := by
  exact heappop_succeeds_under domain (fun _ => True) comparable.under_true
    heap address root rest (fun _ _ _ => True.intro) trivial typed found

end FormalSW.PyAst.Heapq
