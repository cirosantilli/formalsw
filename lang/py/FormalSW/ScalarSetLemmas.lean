import lang.py.FormalSW.ScalarSets

/-! Exact representative lists for sets constructed from homogeneous integers. -/
namespace FormalSW.PyAst.ScalarSet

private abbrev integerKeys (items : List Int) := items.map Constant.int

private def insertUnique (items : List Int) (value : Int) : List Int :=
  if value ∈ items then items else items ++ [value]

private theorem fold_integerKeys (items before : List Int) :
    (integerKeys items).foldl ScalarSet.insert (integerKeys before) = integerKeys (items.foldl insertUnique before) := by
  induction items generalizing before with
  | nil => rfl
  | cons head tail ih =>
      change (integerKeys tail).foldl ScalarSet.insert (ScalarSet.insert (integerKeys before) (.int head)) =
        integerKeys (tail.foldl insertUnique (insertUnique before head))
      rw [ScalarSet.insert_ints]
      exact ih _

private theorem fold_insert (items before : List Int) :
    items.foldl insertUnique before.eraseDups = (before ++ items).eraseDups := by
  induction items generalizing before with
  | nil => simp
  | cons head tail ih =>
      have added : insertUnique before.eraseDups head = (before ++ [head]).eraseDups := by
        by_cases present : head ∈ before <;>
          simp [insertUnique, List.eraseDups_append, List.removeAll, List.eraseDups_cons, present]
      rw [List.foldl_cons, added, ih]
      simp

/-- Constructing an integer set retains the first occurrence of each value. -/
theorem fold_insert_ints (items : List Int) :
    (items.map Constant.int).foldl insert [] = items.eraseDups.map Constant.int := by
  simpa using (fold_integerKeys items []).trans (congrArg integerKeys (fold_insert items []))

private theorem eraseDups_cast (items : List Nat) :
    (items.map (fun n : Nat => (n : Int))).eraseDups = items.eraseDups.map (fun n : Nat => (n : Int)) := by
  cases items with
  | nil => rfl
  | cons head tail =>
      have filtered : (tail.map (fun n : Nat => (n : Int))).filter (fun n => !(n == (head : Int))) =
          (tail.filter (fun n => !(n == head))).map (fun n : Nat => (n : Int)) := by
        rw [List.filter_map]
        congr 1
        apply List.filter_congr
        intro n member
        apply congrArg Bool.not
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq, Int.ofNat_inj]
      simp only [List.map_cons, List.eraseDups_cons]
      rw [filtered, eraseDups_cast (tail.filter (fun n => !(n == head)))]
termination_by items.length
decreasing_by
  have := List.length_filter_le (fun n => !(n == head)) tail
  simp only [List.length_cons]
  omega

/-- Natural-number encodings retain the first occurrence of each integer value. -/
theorem fold_insert_nats (items : List Nat) :
    (items.map (fun n : Nat => Constant.int n)).foldl insert [] =
      items.eraseDups.map (fun n : Nat => Constant.int n) := by
  have built := fold_insert_ints (items.map (fun n : Nat => (n : Int)))
  simpa only [List.map_map, Function.comp_def, eraseDups_cast] using built

end FormalSW.PyAst.ScalarSet
