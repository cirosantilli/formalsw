import lang.py.FormalSW.ItemWriteRelocation

/-! Slice coordinates and selection commute with address relocation. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

def sliceCoordinate : Value → Except ExceptionObject (Option Int)
  | .scalar .none => .ok none
  | .scalar (.int value) => .ok (some value)
  | .scalar (.bool value) => .ok (some (if value then 1 else 0))
  | _ => .error ⟨"TypeError", []⟩

def sliceCoordinates (lower upper stride : Value) : Except ExceptionObject Py.Builtin.Slice.Slice :=
  match sliceCoordinate stride with
  | .error exception => .error exception
  | .ok step =>
      if step = some 0 then .error ⟨"ValueError", []⟩
      else match sliceCoordinate lower with
        | .error exception => .error exception
        | .ok start => match sliceCoordinate upper with
            | .error exception => .error exception
            | .ok stop => .ok ⟨start, stop, step⟩

theorem sliceCoordinate_relocates (rename : Nat → Nat) (value : Value) :
    sliceCoordinate (relocateValue rename value) = sliceCoordinate value := by
  cases value <;> rfl

theorem sliceCoordinates_relocates (rename : Nat → Nat) (lower upper stride : Value) :
    sliceCoordinates (relocateValue rename lower) (relocateValue rename upper) (relocateValue rename stride) =
      sliceCoordinates lower upper stride := by
  simp only [sliceCoordinates, sliceCoordinate_relocates]

theorem sliceBounds_result (heap : Heap) (lower upper stride : Value) :
    Mutable.sliceBounds lower upper stride heap = some (sliceCoordinates lower upper stride, heap) := by
  let coordinate : Value → Eval (Option Int) := fun value => match value with
    | .scalar .none => pure none
    | value => some <$> Mutable.integer value
  have normalized : coordinate = fun value heap => some (sliceCoordinate value, heap) := by
    funext value heap
    cases value with
    | ref address => rfl
    | scalar scalar => cases scalar <;> rfl
  change ((do
    let step ← coordinate stride
    if step = some 0 then Mutable.error "ValueError"
    else
      let start ← coordinate lower
      let stop ← coordinate upper
      pure (⟨start, stop, step⟩ : Py.Builtin.Slice.Slice)) : Eval _) heap = _
  rw [normalized]
  cases first : sliceCoordinate stride <;> cases second : sliceCoordinate lower <;>
    cases third : sliceCoordinate upper <;>
    simp [sliceCoordinates, first, second, third, eval_bind, error]
  all_goals split <;> rfl

theorem sliceBounds_relocates (logical physical : Heap) (rename : Nat → Nat) (lower upper stride : Value) :
    Mutable.sliceBounds (relocateValue rename lower) (relocateValue rename upper) (relocateValue rename stride) physical =
      (Mutable.sliceBounds lower upper stride logical).map (fun pair => (pair.1, physical)) := by
  simp only [sliceBounds_result, sliceCoordinates_relocates, Option.map_some]

theorem sliceBounds_heap (heap after : Heap) (lower upper stride : Value)
    (outcome : Except ExceptionObject Py.Builtin.Slice.Slice)
    (executed : Mutable.sliceBounds lower upper stride heap = some (outcome, after)) : after = heap := by
  rw [sliceBounds_result] at executed
  exact (congrArg Prod.snd (Option.some.inj executed)).symm

theorem slice_map {α β : Type} (move : α → β) (items : List α) (bounds : Py.Builtin.Slice.Slice) :
    Py.Builtin.Sequence.slice (items.map move) bounds =
      (Py.Builtin.Sequence.slice items bounds).map (List.map move) := by
  unfold Py.Builtin.Sequence.slice
  simp only [List.length_map]
  cases selected : Py.Builtin.Slice.indexList bounds items.length with
  | error exception => rfl
  | ok indices =>
    change Except.ok (indices.filterMap (fun index => (items.map move)[index]?)) =
      Except.ok ((indices.filterMap (fun index => items[index]?)).map move)
    simp only [List.getElem?_map, List.map_filterMap]

theorem slice_mem {α : Type} (items selected : List α) (bounds : Py.Builtin.Slice.Slice)
    (sliced : Py.Builtin.Sequence.slice items bounds = .ok selected) :
    ∀ value ∈ selected, value ∈ items := by
  unfold Py.Builtin.Sequence.slice at sliced
  cases indices : Py.Builtin.Slice.indexList bounds items.length with
  | error exception => simp [indices, bind, Except.bind] at sliced
  | ok positions =>
    have same : positions.filterMap (fun index => items[index]?) = selected := by
      simpa [indices, bind, pure, Except.bind, Except.pure] using sliced
    rw [← same]
    intro value member
    obtain ⟨index, _, found⟩ := List.mem_filterMap.mp member
    exact List.mem_of_getElem? found

/-- Lift the pure sequence library's errors using the runtime's exact exception policy. -/
def sliceResult {α : Type} (outcome : Py.Builtin.Result α) : Eval α :=
  match outcome with
  | .ok value => pure value
  | .error (.indexError _) => error "IndexError"
  | .error (.valueError _) => error "ValueError"
  | .error (.typeError _) => error "TypeError"
  | .error _ => unsupported

theorem sliceResult_relocates {α β : Type} (move : α → β) (outcome : Py.Builtin.Result α)
    (logical physical : Heap) :
    sliceResult (outcome.map move) physical =
      (sliceResult outcome logical).map (fun pair => (pair.1.map move, physical)) := by
  cases outcome with
  | ok value => rfl
  | error exception => cases exception <;> rfl

theorem sliceResult_heap {α : Type} (heap after : Heap) (outcome : Py.Builtin.Result α)
    (result : Except ExceptionObject α) (executed : sliceResult outcome heap = some (result, after)) : after = heap := by
  cases outcome with
  | ok value => exact (congrArg Prod.snd (Option.some.inj executed)).symm
  | error exception =>
    cases exception <;> simp [sliceResult, error, unsupported] at executed
    all_goals exact executed.2.symm

theorem sliceResult_ok {α : Type} (heap : Heap) (outcome : Py.Builtin.Result α) (value : α)
    (executed : sliceResult outcome heap = some (.ok value, heap)) : outcome = .ok value := by
  cases outcome with
  | ok result => simpa [sliceResult] using executed
  | error exception => cases exception <;> simp [sliceResult, error, unsupported] at executed

theorem setMany_map {α β : Type} (move : α → β) (indices : List Nat) (replacement items : List α) :
    ((indices.zip (replacement.map move)).foldl (fun result pair => result.set pair.1 pair.2) (items.map move)) =
      ((indices.zip replacement).foldl (fun result pair => result.set pair.1 pair.2) items).map move := by
  induction indices generalizing replacement items with
  | nil => rfl
  | cons index indices ih =>
    cases replacement with
    | nil => rfl
    | cons value replacement =>
      simpa only [List.map_cons, List.zip_cons_cons, List.foldl_cons, List.map_set] using
        ih replacement (items.set index value)

theorem setSlice_map {α β : Type} (move : α → β) (items replacement : List α) (bounds : Py.Builtin.Slice.Slice) :
    Py.Builtin.List.setSlice (items.map move) bounds (replacement.map move) =
      (Py.Builtin.List.setSlice items bounds replacement).map (List.map move) := by
  unfold Py.Builtin.List.setSlice
  simp only [List.length_map]
  cases normalized : Py.Builtin.Slice.indices bounds items.length with
  | error exception => rfl
  | ok coordinates =>
    rcases coordinates with ⟨start, stop, step⟩
    by_cases unit : step = 1
    · simp [unit, bind, pure, Except.bind, Except.pure, Except.map, List.map_append, List.map_take, List.map_drop]
    · cases selected : Py.Builtin.Slice.indexList bounds items.length with
      | error exception => simp [unit, bind, Except.bind, Except.map]
      | ok indices =>
        simp only [bind, Except.bind, unit, if_false]
        split <;> simp [pure, Except.pure, Except.map, setMany_map]

theorem setMany_within {α : Type} (predicate : α → Prop) (indices : List Nat) (replacement items : List α)
    (old : ∀ value ∈ items, predicate value) (new : ∀ value ∈ replacement, predicate value) :
    ∀ value ∈ (indices.zip replacement).foldl (fun result pair => result.set pair.1 pair.2) items, predicate value := by
  induction indices generalizing replacement items with
  | nil => exact old
  | cons index indices ih =>
    cases replacement with
    | nil => exact old
    | cons value replacement =>
      apply ih replacement (items.set index value)
      · intro current member
        rcases List.mem_or_eq_of_mem_set member with previous | same
        · exact old current previous
        · exact same ▸ new value (by simp)
      · exact fun current member => new current (List.mem_cons_of_mem _ member)

theorem setSlice_within {α : Type} (predicate : α → Prop) (items replacement updated : List α)
    (bounds : Py.Builtin.Slice.Slice) (old : ∀ value ∈ items, predicate value)
    (new : ∀ value ∈ replacement, predicate value)
    (written : Py.Builtin.List.setSlice items bounds replacement = .ok updated) :
    ∀ value ∈ updated, predicate value := by
  unfold Py.Builtin.List.setSlice at written
  cases normalized : Py.Builtin.Slice.indices bounds items.length with
  | error exception => simp [normalized, bind, Except.bind] at written
  | ok coordinates =>
    rcases coordinates with ⟨start, stop, step⟩
    by_cases unit : step = 1
    · have same : items.take start.toNat ++ replacement ++ items.drop (max start stop).toNat = updated := by
        simpa [normalized, unit, bind, pure, Except.bind, Except.pure] using written
      rw [← same]
      intro value member
      rcases List.mem_append.mp member with left | right
      · rcases List.mem_append.mp left with previous | fresh
        · exact old value (List.mem_of_mem_take previous)
        · exact new value fresh
      · exact old value (List.mem_of_mem_drop right)
    · cases selected : Py.Builtin.Slice.indexList bounds items.length with
      | error exception => simp [normalized, unit, selected, bind, Except.bind] at written
      | ok indices =>
        simp only [normalized, bind, Except.bind, unit, if_false, selected] at written
        split at written
        · cases written
        · have same : (indices.zip replacement).foldl (fun result pair => result.set pair.1 pair.2) items = updated := Except.ok.inj written
          rw [← same]
          exact setMany_within predicate indices replacement items old new

end FormalSW.PyAst.Mutable.Relocation
