import lang.py.FormalSW.HeapRuntimeCostRangeComprehensions

open FormalSW.PyAst HeapCalls HeapCalls.Runtime
open NestedIntList (encode)
private def program : Module := { body := [] }

/-- Negative endpoints produce empty ranges, while every nonempty rectangle
uses a single output array and charges all element additions and resizing. -/
example (rows columns : Int) (heap : Heap) :
    ∃ items : List Int, items.length = rows.toNat*columns.toNat ∧
      EvaluatesIn .word program (fun _ => none)
        (.listComp (.binOp (.name "r") .add (.name "c"))
          [("r", .call (.name "range") [.constant (.int rows)], []),
           ("c", .call (.name "range") [.constant (.int columns)], [])])
        heap ((17*columns.toNat+13)*rows.toNat+13) (.ref heap.length)
        (heap ++ [.list (encode items)]) := by
  obtain ⟨items, env, loop, length, _⟩ := collect_rectangle_loop program heap
    (.binOp (.name "r") .add (.name "c")) (.constant (.int columns)) "r" "c" (by decide)
    rows columns 6 1 (fun _ => True) (by intros; trivial) (by intros; trivial)
    (by intros; exact EvaluatesIn.constant)
    (by
      intro items env r c _ _ _ _ _ getRow getColumn
      exact ⟨r+c, EvaluatesIn.binary (work := 1) (EvaluatesIn.lookup getRow) (EvaluatesIn.lookup getColumn) rfl rfl⟩)
    rows.toNat 0 (by simp) (by omega) []
    (comprehensionEnv (fun _ => none)
      [("r", .call (.name "range") [.constant (.int rows)], []),
       ("c", .call (.name "range") [.constant (.int columns)], [])]) trivial
  refine ⟨items, by simpa using length, ?_⟩
  apply EvaluatesIn.mono (small := 2+3+((17*columns.toNat+13)*rows.toNat+4)+4) (larger := by omega)
  apply EvaluatesIn.list_comp_range (work := 3) (values := [.scalar (.int rows)])
    (start := 0) (stop := rows) (stride := 1) (ArgumentsIn.cons EvaluatesIn.constant ArgumentsIn.nil) rfl rfl
  exact loop
