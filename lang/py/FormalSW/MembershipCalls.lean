import lang.py.FormalSW.HeapCalls

/-! Sequence membership proofs for arbitrary integer inputs and shared heaps. -/
namespace FormalSW.PyAst.HeapCalls

/-- Scalar set membership uses Python equality, including the equality of True and 1. -/
theorem membership_set (heap : Mutable.Heap) (address : Nat) (needle : Constant) (items : List Constant)
    (found : heap[address]? = some (.set items)) (negated : Bool) :
    membership (.scalar needle) (.ref address) negated heap =
      some (.ok (.scalar (.bool (if negated then !ScalarSet.contains items needle
        else ScalarSet.contains items needle))), heap) := by
  simp [membership, found]

theorem sequenceContains_ints (heap : Mutable.Heap) (needle : Int) (items : List Int) :
    sequenceContains (.scalar (.int needle)) (items.map (fun n => .scalar (.int n))) heap =
      some (.ok (decide (needle ∈ items)), heap) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      by_cases same : head = needle
      · subst head
        simp [sequenceContains]
      · simp [sequenceContains, same, compare, scalarCompare, evalCmpOp, Mutable.truth, scalarTruth, ih, Ne.symm same]

theorem membership_list_ints (heap : Mutable.Heap) (address : Nat) (needle : Int) (items : List Int)
    (found : heap[address]? = some (.list (items.map (fun n => .scalar (.int n))))) (negated : Bool) :
    membership (.scalar (.int needle)) (.ref address) negated heap =
      some (.ok (.scalar (.bool (if negated then !decide (needle ∈ items) else decide (needle ∈ items)))), heap) := by
  simp [membership, found, sequenceContains_ints, Except.map]

theorem membership_tuple_ints (heap : Mutable.Heap) (address : Nat) (needle : Int) (items : List Int)
    (found : heap[address]? = some (.tuple (items.map (fun n => .scalar (.int n))))) (negated : Bool) :
    membership (.scalar (.int needle)) (.ref address) negated heap =
      some (.ok (.scalar (.bool (if negated then !decide (needle ∈ items) else decide (needle ∈ items)))), heap) := by
  simp [membership, found, sequenceContains_ints, Except.map]

end FormalSW.PyAst.HeapCalls
