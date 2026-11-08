import lang.py.FormalSW.HeapSetWork

/-! A comparison-sort library tariff for scalar sequences, including output
copying. It describes the target library algorithm, not the insertion sort used
to define observable ordering in Lean. Object comparison callbacks are unpriced. -/
namespace FormalSW.PyAst.HeapCalls.SortWork
open PrimitiveWork

def scalars (items : List Mutable.Value) : Option (List Constant) :=
  items.mapM fun item => match item with | .scalar value => some value | .ref _ => none

def sorting (arithmetic : Arithmetic) (items : List Constant) : Nat :=
  comparisonSort items.length (2 * SetWork.width arithmetic items) + sequenceCopy items.length

def operation (arithmetic : Arithmetic) (heap : Mutable.Heap) (values : List Mutable.Value) : Option Nat :=
  match values with
  | [.ref address] => match heap[address]? with
      | some (.list items) | some (.tuple items) => (scalars items).map (sorting arithmetic)
      | _ => none
  | _ => none

theorem scalars_map (items : List Constant) : scalars (items.map Mutable.Value.scalar) = some items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      simp only [scalars, List.map_cons, List.mapM_cons] at ih ⊢
      simp only [ih]
      rfl

theorem sorting_ints (items : List Int) :
    sorting .word (items.map Constant.int) =
      (items.length + 1) * (Nat.log2 (items.length + 1) + 1) * 3 + (items.length + 1) := by
  simp [sorting, comparisonSort, sequenceCopy, SetWork.width_ints]

end FormalSW.PyAst.HeapCalls.SortWork
