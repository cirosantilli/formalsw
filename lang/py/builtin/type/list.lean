import lang.py.builtin.type.sequence

/-! Python's mutable list operations, modeled as pure list transformations. -/

namespace FormalSW.Py.Builtin.List

open FormalSW.Py.Builtin

abbrev ListValue (α : Type u) := List α

def empty : ListValue α := []
def ofIterable (values : List α) : ListValue α := values
def size (values : ListValue α) : Nat := values.length
def count [BEq α] (values : ListValue α) (needle : α) : Nat := Sequence.count values needle
def index [BEq α] (values : ListValue α) (needle : α) : Result Nat :=
  match Sequence.index? values needle with
  | some position => .ok position
  | none => .error (.valueError "value is not in list")
def append (values : ListValue α) (value : α) : ListValue α := values ++ [value]
def clear (_ : ListValue α) : ListValue α := []
def copy (values : ListValue α) : ListValue α := values
def extend (values additional : ListValue α) : ListValue α := values ++ additional

def insert (values : ListValue α) (index : Int) (value : α) : ListValue α :=
  let shifted := if index < 0 then index + values.length else index
  let normalized := Int.toNat (max 0 (min shifted values.length))
  values.take normalized ++ value :: values.drop normalized

def pop (values : ListValue α) (index : Int := -1) : Result (α × ListValue α) := do
  let normalized ← match Sequence.normalizeIndex values.length index with
    | some value => .ok value
    | none => .error (.indexError "pop index out of range")
  let value ← match values[normalized]? with
    | some value => .ok value
    | none => .error (.indexError "pop index out of range")
  return (value, values.take normalized ++ values.drop (normalized + 1))

/-- A valid nonnegative index removes exactly that occurrence. -/
theorem pop_getElem (values : ListValue α) (position : Nat) (valid : position < values.length) :
    pop values position = .ok (values[position], values.eraseIdx position) := by
  have nonnegative : ¬ (position : Int) < 0 := by omega
  have bounded : ¬ (values.length : Int) ≤ position := by omega
  have normalized : Sequence.normalizeIndex values.length position = some position := by
    simp [Sequence.normalizeIndex, nonnegative, bounded, Int.toNat_natCast]
  unfold pop
  rw [normalized]
  change (match values[position]? with
    | some value => Except.ok (value, values.take position ++ values.drop (position + 1))
    | none => Except.error (Error.indexError "pop index out of range")) = _
  simp [valid, List.eraseIdx_eq_take_drop_succ]

def remove [BEq α] (values : ListValue α) (needle : α) : Result (ListValue α) :=
  match Sequence.index? values needle with
  | none => .error (.valueError "list.remove(x): x not in list")
  | some index => .ok (values.take index ++ values.drop (index + 1))

def reverse (values : ListValue α) : ListValue α := values.reverse

def setAt (values : ListValue α) (index : Int) (value : α) : Result (ListValue α) :=
  match Sequence.normalizeIndex values.length index with
  | none => .error (.indexError "list assignment index out of range")
  | some normalized => .ok (values.set normalized value)

def deleteAt (values : ListValue α) (index : Int) : Result (ListValue α) :=
  match Sequence.normalizeIndex values.length index with
  | none => .error (.indexError "list assignment index out of range")
  | some normalized => .ok (values.take normalized ++ values.drop (normalized + 1))

def setSlice (values : ListValue α) (bounds : Slice.Slice) (replacement : List α) :
    Result (ListValue α) := do
  let (start, stop, step) ← Slice.indices bounds values.length
  if step = 1 then
    return values.take start.toNat ++ replacement ++ values.drop (max start stop).toNat
  else
    let indices ← Slice.indexList bounds values.length
    if indices.length != replacement.length then
      .error (.valueError "attempt to assign sequence of size mismatch to extended slice")
    else
      return (indices.zip replacement).foldl (fun result pair => result.set pair.1 pair.2) values

/-- Replacing selected elements preserves the sequence length. -/
theorem length_setMany (updates : List (Nat × α)) (values : List α) :
    (updates.foldl (fun result pair => result.set pair.1 pair.2) values).length = values.length := by
  induction updates generalizing values with
  | nil => rfl
  | cons update rest ih => simpa only [List.foldl_cons, List.length_set] using ih (values.set update.1 update.2)

/-- Uniform updates change precisely the selected positions; duplicates are harmless. -/
theorem getElem?_setUniform (indices : List Nat) (values : List α) (value : α) (index : Nat)
    (valid : index < values.length) :
    (indices.foldl (fun result position => result.set position value) values)[index]? =
      if index ∈ indices then some value else values[index]? := by
  induction indices generalizing values with
  | nil => simp
  | cons position rest ih =>
      rw [List.foldl_cons, ih _ (by simpa using valid)]
      by_cases selected : index ∈ rest
      · simp [selected]
      · by_cases same : position = index
        · subst position
          simp [selected, List.getElem?_set_self valid]
        · simp [selected, List.getElem?_set_ne same, Ne.symm same]

private theorem setMany_uniform (indices : List Nat) (value : α) (values : List α) :
    ((indices.zip (List.replicate indices.length value)).foldl
      (fun result pair => result.set pair.1 pair.2) values) =
      indices.foldl (fun result index => result.set index value) values := by
  induction indices generalizing values with
  | nil => rfl
  | cons index rest ih => simpa using ih (values.set index value)

/-- A uniform extended-slice assignment sets exactly its selected positions. -/
theorem setSlice_uniform (values : List α) (bounds : Slice.Slice) (value : α)
    (normalized : Slice.indices bounds values.length = .ok (start, stop, step))
    (extended : step ≠ 1)
    (selected : Slice.indexList bounds values.length = .ok indices) :
    setSlice values bounds (List.replicate indices.length value) =
      .ok (indices.foldl (fun result index => result.set index value) values) := by
  simp [setSlice, normalized, extended, selected, setMany_uniform, bind, pure, Except.bind, Except.pure]

def deleteSlice (values : ListValue α) (bounds : Slice.Slice) : Result (ListValue α) := do
  let indices ← Slice.indexList bounds values.length
  return values.mapIdx (fun index value => (index, value))
    |>.filter (fun pair => !indices.contains pair.1)
    |>.map Prod.snd

theorem deleteSlice_empty (values : List α) (bounds : Slice.Slice)
    (selected : Slice.indexList bounds values.length = .ok []) :
    deleteSlice values bounds = .ok values := by
  simp [deleteSlice, selected, bind, pure, Except.bind, Except.pure]
  rw [List.filter_eq_self.mpr (by simp)]
  apply List.ext_getElem?
  intro index
  simp [List.getElem?_mapIdx, Option.map_map, Function.comp_def]

/-- Stable insertion sort using only the supplied strict-less comparison. -/
private def insertSorted (less : α → α → Bool) (value : α) : List α → List α
  | [] => [value]
  | head :: tail =>
      if less value head then value :: head :: tail
      else head :: insertSorted less value tail

def sort (values : ListValue α) (less : α → α → Bool)
    (reverseOrder : Bool := false) : ListValue α :=
  let ordering := if reverseOrder then (fun left right => less right left) else less
  values.foldl (fun result value => insertSorted ordering value result) []

end FormalSW.Py.Builtin.List
