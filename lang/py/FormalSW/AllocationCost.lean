import lang.py.FormalSW.HeapCalls
import lang.py.FormalSW.WeightedExecutionCost

/-! A weighted heap model: one unit per transition plus each net new list slot.
This charges list slicing and concatenation by allocated length. It is not a
complete CPython allocator model and does not charge scalar arithmetic by bits. -/
namespace FormalSW.PyAst.HeapCalls.AllocationCost

/-- Number of list-element slots in the modeled heap, including unreachable objects. -/
def listSlots (heap : Heap) : Nat :=
  (heap.map fun object => match object with | .list values => values.length | _ => 0).sum

@[simp] theorem listSlots_append (left right : Heap) :
    listSlots (left ++ right) = listSlots left + listSlots right := by
  simp [listSlots, List.map_append, List.sum_append]

@[simp] theorem listSlots_singleton (values : List Value) :
    listSlots [.list values] = values.length := by simp [listSlots]

def finalSlots : Except ExceptionObject Completion → Nat
  | .ok completion => listSlots completion.heap
  | .error _ => 0

/-- Count allocations in the actual next state, not the syntactic number of calls. -/
def charge (module : Module) (anchors : Nat) (state : State) : Nat :=
  1 + match step module anchors state with
    | .next following => listSlots following.heap - listSlots state.heap
    | .done outcome => finalSlots outcome - listSlots state.heap
    | .unsupported => 0

/-- Every terminating weighted trace pays for its increase in allocated list slots. -/
theorem allocated_le (run : FinishesWith (step module anchors) (charge module anchors) state cost outcome) :
    finalSlots outcome ≤ listSlots state.heap + cost := by
  have bound (a b : Nat) : a ≤ b + (1 + (a - b)) := by omega
  apply run.potential (fun state => listSlots state.heap) finalSlots
  · intro s result finished
    simp only [charge, finished]
    exact bound _ _
  · intro s next transition
    simp only [charge, transition]
    exact bound _ _

/-- Erasing weights preserves precisely the same source interpreter and completion. -/
theorem cost_exists (run : Finishes (step module anchors) state outcome) :
    ∃ cost, FinishesWith (step module anchors) (charge module anchors) state cost outcome :=
  run.exists_weighted_cost _

/-- Heap-preserving transitions have unit charge in the allocation model. -/
theorem next_same_heap (transition : step module anchors initial = .next following)
    (sameHeap : initial.heap = following.heap)
    (rest : ReachesWith (step module anchors) (charge module anchors) following cost final) :
    ReachesWith (step module anchors) (charge module anchors) initial (cost + 1) final := by
  have unitCharge : charge module anchors initial = 1 := by simp [charge, transition, sameHeap]
  simpa [unitCharge, Nat.add_comm] using ReachesWith.next transition rest

/-- Returning a value without allocating pays only the final transition. -/
theorem finish_value (module : Module) (anchors : Nat) (value : Value) (heap : Heap) :
    FinishesWith (step module anchors) (charge module anchors) ⟨.value value, [], heap⟩ 1
      (.ok ⟨.ok value, [], heap, anchors⟩) := by
  have terminal : step module anchors ⟨.value value, [], heap⟩ = .done (.ok ⟨.ok value, [], heap, anchors⟩) := rfl
  have unitCharge : charge module anchors ⟨.value value, [], heap⟩ = 1 := by simp [charge, terminal, finalSlots]
  have run := FinishesWith.done (step := step module anchors)
    (state := ⟨.value value, [], heap⟩) (charge := charge module anchors) terminal
  simpa [unitCharge] using run

end FormalSW.PyAst.HeapCalls.AllocationCost
