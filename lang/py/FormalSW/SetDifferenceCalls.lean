import lang.py.FormalSW.HeapCalls
import lang.py.FormalSW.ScalarSetLemmas

/-! Integer-set construction, membership, cardinality, and source subtraction rules. -/
namespace FormalSW.PyAst

namespace IntegerSets

def entries (values : List Int) : List Constant := values.eraseDups.map Constant.int
def encoded (values : List Int) : List Mutable.Value :=
  values.map (fun value => .scalar (.int value))

theorem contains_entries (values : List Int) (value : Int) :
    ScalarSet.contains (entries values) (.int value) = decide (value ∈ values) := by
  simp [entries, ScalarSet.contains_ints]

theorem entries_length (values : List Int) : (entries values).length = values.eraseDups.length := by
  simp [entries]

private theorem erased_sublist (values : List Int) : values.eraseDups.Sublist values := by
  cases values with
  | nil => exact .refl _
  | cons first rest =>
      rw [List.eraseDups_cons]
      exact (erased_sublist (rest.filter (fun value => !(value == first)))).trans
        List.filter_sublist |>.cons_cons first
termination_by values.length
decreasing_by
  have := List.length_filter_le (fun value => !(value == first)) rest
  simp only [List.length_cons]
  omega

private theorem erased_nodup (values : List Int) : values.eraseDups.Nodup := by
  cases values with
  | nil => exact .nil
  | cons first rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      refine ⟨?_, erased_nodup (rest.filter (fun value => !(value == first)))⟩
      intro member
      have impossible := (List.mem_filter.mp (List.mem_eraseDups.mp member)).2
      simp at impossible
termination_by values.length
decreasing_by
  have := List.length_filter_le (fun value => !(value == first)) rest
  simp only [List.length_cons]
  omega

private theorem erased_of_nodup (values : List Int) (distinct : values.Nodup) :
    values.eraseDups = values := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      have separated := List.nodup_cons.mp distinct
      have filtered : rest.filter (fun value => !(value == first)) = rest := by
        apply List.filter_eq_self.mpr
        intro value member
        have different : value ≠ first := by
          intro same
          subst value
          exact separated.1 member
        simp [different]
      rw [List.eraseDups_cons, filtered, ih separated.2]

theorem entries_length_eq (values : List Int) :
    (entries values).length = values.length ↔ values.Nodup := by
  rw [entries_length]
  constructor
  · intro length
    have same := (erased_sublist values).eq_of_length length
    rw [← same]
    exact erased_nodup _
  · intro distinct
    rw [erased_of_nodup values distinct]

theorem compare_ints_eq (left right : List Int) :
    ScalarSet.compare .eq (left.map Constant.int) (right.map Constant.int) = true ↔
      ∀ value, value ∈ left ↔ value ∈ right := by
  simp only [ScalarSet.compare, ScalarSet.subset, Bool.and_eq_true,
    List.all_map, Function.comp_def, ScalarSet.contains_ints, List.all_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨forward, backward⟩ value
    exact ⟨forward value, backward value⟩
  · intro same
    exact ⟨fun value member => (same value).mp member, fun value member => (same value).mpr member⟩

theorem compare_eq (left right : List Int) :
    ScalarSet.compare .eq (entries left) (entries right) = true ↔
      ∀ value, value ∈ left ↔ value ∈ right := by
  simpa only [entries, List.mem_eraseDups] using compare_ints_eq left.eraseDups right.eraseDups

theorem difference_entries (left right : List Int) :
    ScalarSet.difference (entries left) (entries right) =
      (left.eraseDups.filter (fun value => decide (value ∉ right))).map Constant.int := by
  simp only [entries, ScalarSet.difference_ints, List.mem_eraseDups]

theorem contains_difference (left right : List Int) (value : Int) :
    ScalarSet.contains (ScalarSet.difference (entries left) (entries right)) (.int value) =
      decide (value ∈ left ∧ value ∉ right) := by
  simp [entries, ScalarSet.contains_difference_ints]

end IntegerSets

namespace Mutable

def scalarSequence (tuple : Bool) (items : List Constant) : Object :=
  if tuple then .tuple (items.map Value.scalar) else .list (items.map Value.scalar)

theorem allocateSetValues_scalars (heap : Heap) (items : List Constant) :
    allocateSetValues (items.map Value.scalar) heap =
      some (.ok (.ref heap.length), heap ++ [.set (items.foldl ScalarSet.insert [])]) := by
  have keys : (items.map Value.scalar).mapM setKey = (pure items : Eval (List Constant)) := by
    induction items with
    | nil => rfl
    | cons item rest ih => simp only [List.map_cons, List.mapM_cons, setKey, ih]; rfl
  unfold allocateSetValues
  split
  · rw [keys]
    rfl
  · rename_i bad
    exfalso
    clear keys
    revert bad
    induction items with
    | nil => intro bad; exact bad rfl
    | cons item rest ih => intro bad; exact ih bad

theorem setFrom_scalar_sequence (heap : Heap) (address : Nat) (tuple : Bool) (items : List Constant)
    (found : heap[address]? = some (scalarSequence tuple items)) :
    setFrom (.ref address) heap =
      some (.ok (.ref heap.length), heap ++ [.set (items.foldl ScalarSet.insert [])]) := by
  have read : setFrom (.ref address) heap = allocateSetValues (items.map Value.scalar) heap := by
    cases tuple <;> simp [scalarSequence] at found <;> simp [setFrom, sequence, found] <;> rfl
  rw [read, allocateSetValues_scalars]

theorem setFrom_integer_sequence (heap : Heap) (address : Nat) (tuple : Bool) (items : List Int)
    (found : heap[address]? = some (scalarSequence tuple (items.map Constant.int))) :
    setFrom (.ref address) heap =
      some (.ok (.ref heap.length), heap ++ [.set (IntegerSets.entries items)]) := by
  simpa only [ScalarSet.fold_insert_ints, IntegerSets.entries] using
    setFrom_scalar_sequence heap address tuple (items.map Constant.int) found

end Mutable

namespace HeapCalls.Evaluates

variable {module : Module} {env : HeapCalls.Env} {heap middle afterRight : Mutable.Heap}
  {expression leftExpression rightExpression : Expr} {address leftAddress rightAddress : Nat}
  {tuple : Bool} {items leftItems rightItems : List Int}

theorem set_integer_sequence
    (evaluated : Evaluates module env expression heap (.ref address) middle)
    (found : middle[address]? = some (Mutable.scalarSequence tuple (items.map Constant.int))) :
    Evaluates module env (.builtinCall .set [expression]) heap (.ref middle.length)
      (middle ++ [.set (IntegerSets.entries items)]) := by
  apply Evaluates.builtin (.cons evaluated .nil)
  exact Mutable.setFrom_integer_sequence middle address tuple items found

theorem difference_integer_sets
    (left : Evaluates module env leftExpression heap (.ref leftAddress) middle)
    (right : Evaluates module env rightExpression middle (.ref rightAddress) afterRight)
    (leftFound : afterRight[leftAddress]? = some (.set (IntegerSets.entries leftItems)))
    (rightFound : afterRight[rightAddress]? = some (.set (IntegerSets.entries rightItems))) :
    Evaluates module env (.binOp leftExpression .sub rightExpression) heap (.ref afterRight.length)
      (afterRight ++ [.set (ScalarSet.difference
        (IntegerSets.entries leftItems) (IntegerSets.entries rightItems))]) :=
  Evaluates.binary left right
    (Mutable.binary_difference_sets afterRight leftAddress rightAddress _ _ leftFound rightFound)

end HeapCalls.Evaluates
end FormalSW.PyAst
