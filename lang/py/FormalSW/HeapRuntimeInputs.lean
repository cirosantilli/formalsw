import lang.py.FormalSW.HeapRuntimeCost

/-! Canonical input heaps keep the growth measure independent of list contents.
Each row is represented by a separate object; empty and ragged inputs are allowed. -/
namespace FormalSW.PyAst.HeapCalls.Runtime.NestedIntList
open PrimitiveWork

abbrev encode (values : List Int) : List Mutable.Value :=
  values.map (fun value => .scalar (.int value))

def heap (rows : List (List Int)) : Mutable.Heap :=
  .list ((List.range rows.length).map (fun i => .ref (i+1))) ::
    rows.map (fun row => .list (encode row))

/-- Charge the outer traversal even when every row is empty. -/
def size (rows : List (List Int)) : Nat := rows.length + (rows.map List.length).sum

theorem root (rows : List (List Int)) :
    (heap rows)[0]? = some (.list ((List.range rows.length).map (fun i => .ref (i+1)))) := rfl

theorem row (rows : List (List Int)) (i : Nat) (valid : i < rows.length) :
    (heap rows)[i+1]? = some (.list (encode rows[i])) := by
  simp [heap, List.getElem?_eq_getElem valid]

theorem rows_le_size (rows : List (List Int)) : rows.length ≤ size rows := by
  simp [size]

theorem potential_bound (rows : List (List Int)) : heapPotential (heap rows) ≤ 2*size rows := by
  have lists : ∀ rows : List (List Int),
      ((rows.map (fun row => Mutable.Object.list (encode row))).map objectPotential).sum ≤
        2*(rows.map List.length).sum := by
    intro rows
    induction rows with
    | nil => simp
    | cons row rows ih =>
        simp only [List.map_cons, List.sum_cons, objectPotential, List.length_map] at *
        have credit := Nat.sub_le (2*row.length) (DynamicArray.capacity row.length)
        unfold DynamicArray.potential at *
        omega
  have credit := Nat.sub_le (2*rows.length) (DynamicArray.capacity rows.length)
  have rest := lists rows
  simp only [heap, heapPotential, List.map_cons, List.sum_cons, objectPotential,
    List.length_map, List.length_range, size, Nat.mul_add]
  unfold DynamicArray.potential at *
  omega

end FormalSW.PyAst.HeapCalls.Runtime.NestedIntList
