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

/-- Pair each input row with its address in the canonical heap. -/
def bindings (rows : List (List Int)) : List (Nat × List Int) :=
  rows.zipIdx.map (fun pair => (pair.2+1, pair.1))

theorem bindings_values (rows : List (List Int)) : (bindings rows).map Prod.snd = rows := by
  simp [bindings, List.map_map, Function.comp_def]

theorem bindings_root (rows : List (List Int)) :
    (heap rows)[0]? = some (.list ((bindings rows).map (fun pair => .ref pair.1))) := by
  have indices := List.zipIdx_map_snd 0 rows
  have mapped := congrArg (List.map (fun i => Mutable.Value.ref (i+1))) indices
  rw [← List.range_eq_range'] at mapped
  rw [root]
  congr 2
  simpa only [bindings, List.map_map, Function.comp_def] using mapped.symm

theorem bindings_row (rows : List (List Int)) (pair : Nat × List Int) (member : pair ∈ bindings rows) :
    (heap rows)[pair.1]? = some (.list (encode pair.2)) := by
  unfold bindings at member
  obtain ⟨⟨values, index⟩, indexed, equal⟩ := List.mem_map.mp member
  subst pair
  obtain ⟨valid, same⟩ := List.mem_zipIdx' indexed
  simpa only [same] using row rows index valid

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
