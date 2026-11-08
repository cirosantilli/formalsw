import lang.py.FormalSW.HeapRuntimeCost

/-! Canonical input heaps and explicit size measures for list families.
Nested rows are separate objects; strings retain their Unicode character lengths. -/
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

theorem typed (rows : List (List Int)) :
    Mutable.Value.HasType (heap rows) (.ref 0) "list[list[int]]" := by
  refine ⟨(bindings rows).map (fun pair => .ref pair.1), bindings_root rows,
    Or.inr ⟨"list[int]", rfl, ?_⟩⟩
  intro item member
  obtain ⟨pair, pairMember, rfl⟩ := List.mem_map.mp member
  refine ⟨by rw [String.startsWith_string_iff]; decide, ?_⟩
  rw [Mutable.Value.ListHasType]
  refine ⟨encode pair.2, bindings_row rows pair pairMember, Or.inr ⟨"int", rfl, ?_⟩⟩
  intro value member
  obtain ⟨integer, _, rfl⟩ := List.mem_map.mp member
  rfl

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

namespace FormalSW.PyAst.HeapCalls.Runtime.StringList
open PrimitiveWork

def encode (values : List String) : List Mutable.Value :=
  values.map (fun value => .scalar (.string value))

def heap (values : List String) : Mutable.Heap := [.list (encode values)]

/-- Include list slots so a list of empty strings still has nonzero size. -/
def size (values : List String) : Nat := values.length + (values.map String.length).sum

theorem typed (values : List String) : Mutable.Value.HasType (heap values) (.ref 0) "list[str]" := by
  refine ⟨encode values, rfl, Or.inr ⟨"str", rfl, ?_⟩⟩
  intro value member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  rfl

@[simp] theorem size_nil : size [] = 0 := rfl

@[simp] theorem size_cons (text : String) (rest : List String) :
    size (text :: rest) = text.length + 1 + size rest := by
  simp only [size, List.length_cons, List.map_cons, List.sum_cons]
  omega

theorem length_le_size (values : List String) : values.length ≤ size values := by
  simp [size]

theorem member_length_le_size (values : List String) (text : String) (member : text ∈ values) :
    text.length + 1 ≤ size values := by
  induction values with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · have bound := ih member
        rw [size_cons]
        omega

theorem size_perm {left right : List String} (perm : left.Perm right) : size left = size right := by
  induction perm with
  | nil => rfl
  | cons _ _ ih => simp only [size_cons]; omega
  | swap _ _ _ => simp only [size_cons]; omega
  | trans _ _ first second => exact first.trans second

theorem potential_bound (values : List String) : heapPotential (heap values) ≤ 2 * size values := by
  have credit := DynamicArray.potential_le values.length
  have length := length_le_size values
  simp only [heap, encode, heapPotential, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, objectPotential, List.length_map]
  omega

end FormalSW.PyAst.HeapCalls.Runtime.StringList
