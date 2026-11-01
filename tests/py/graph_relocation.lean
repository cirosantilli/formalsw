import lang.py.FormalSW.MutableRelocation

/-! Structural regressions for cycles that cross the entry/allocation boundary. -/
namespace GraphRelocationExamples
open FormalSW.PyAst Mutable Mutable.Relocation Graph.Relocation

private def logicalHeap (payload : Int) : Heap :=
  [.list [.ref 2, .ref 2, .scalar (.int payload)], .tuple [.ref 0], .list [.ref 1]]

private def shifted (index : Nat) : Nat := if index = 0 then 0 else index + 1

private def physicalHeap (payload : Int) (hidden : Object) : Heap :=
  [.list [.ref 3, .ref 3, .scalar (.int payload)], hidden, .tuple [.ref 0], .list [.ref 2]]

private theorem left_layout (payload : Int) (extra : Heap) :
    HeapLayout (logicalHeap payload) (logicalHeap payload ++ extra) id := by
  constructor
  · intro i _ j _ same
    exact same
  · intro index node found
    have bound : index < 3 := by
      simpa [logicalHeap] using (List.getElem?_eq_some_iff.mp found).1
    have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases cases with rfl | rfl | rfl <;>
      simp [logicalHeap, graphNode] at found <;> subst node <;>
      simp [logicalHeap, graphNode, relocateNode, relocateEdge, Mutable.Value.edge]

private theorem right_layout (payload : Int) (hidden : Object) (extra : Heap) :
    HeapLayout (logicalHeap payload) (physicalHeap payload hidden ++ extra) shifted := by
  constructor
  · intro i _ j _ same
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp_all [shifted] <;> omega
  · intro index node found
    have bound : index < 3 := by
      simpa [logicalHeap] using (List.getElem?_eq_some_iff.mp found).1
    have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases cases with rfl | rfl | rfl <;>
      simp [logicalHeap, graphNode] at found <;> subst node <;>
      simp [physicalHeap, graphNode, shifted, relocateNode, relocateEdge, Mutable.Value.edge]

/-- The caller's cell 0 points twice to a fresh cell; discovery is 0, 2, 1,
then back to 0. Private allocations are arbitrary and the result may be exceptional. -/
theorem relocated_cycle (payload : Int) (hidden : Object) (leftExtra rightExtra : Heap)
    (outcome : Except ExceptionObject Mutable.Value)
    (within : ∀ value, outcome = .ok value → value.edge.Within 3) :
    Completion.Equivalent
      ⟨outcome, [("shared", .ref 2)], logicalHeap payload ++ leftExtra, 1⟩
      ⟨outcome.map (relocateValue shifted), [("shared", .ref 3)],
        physicalHeap payload hidden ++ rightExtra, 1⟩ := by
  let logical : Completion := ⟨outcome, [("shared", .ref 2)], logicalHeap payload, 1⟩
  apply equivalent_completions logical _ _ id shifted
  · refine ⟨left_layout payload leftExtra, rfl, ?_, rfl, ?_⟩
    · intros; rfl
    · cases outcome with
      | error error => rfl
      | ok value => cases value <;> rfl
  · refine ⟨right_layout payload hidden rightExtra, rfl, ?_, rfl, rfl⟩
    intro address bound
    have zero : address = 0 := by change address < 1 at bound; omega
    simp [shifted, zero]
  · simp [logical, logicalHeap, Heap.Valid]
  · simp [logical, logicalHeap]
  · simp [logical, logicalHeap, Value.edge, Graph.Edge.Within]
  · simpa only [logical, logicalHeap, List.length_cons, List.length_nil] using within

/-- Returning the aliased fresh object is covered for every scalar payload. -/
example (payload : Int) (hidden : Object) (leftExtra rightExtra : Heap) :
    Completion.Equivalent
      ⟨.ok (.ref 2), [("shared", .ref 2)], logicalHeap payload ++ leftExtra, 1⟩
      ⟨.ok (.ref 3), [("shared", .ref 3)], physicalHeap payload hidden ++ rightExtra, 1⟩ := by
  apply relocated_cycle payload hidden leftExtra rightExtra (.ok (.ref 2))
  intro value same
  cases same
  exact Nat.lt_succ_self 2

/-- Exceptions retain the same shared cyclic state, with no result root. -/
example (payload : Int) (hidden : Object) (leftExtra rightExtra : Heap) (error : ExceptionObject) :
    Completion.Equivalent
      ⟨.error error, [("shared", .ref 2)], logicalHeap payload ++ leftExtra, 1⟩
      ⟨.error error, [("shared", .ref 3)], physicalHeap payload hidden ++ rightExtra, 1⟩ := by
  apply relocated_cycle payload hidden leftExtra rightExtra (.error error)
  intro value impossible
  cases impossible

#print axioms Graph.Relocation.equivalent_layouts
#print axioms Mutable.Relocation.equivalent_completions
#print axioms relocated_cycle
end GraphRelocationExamples
