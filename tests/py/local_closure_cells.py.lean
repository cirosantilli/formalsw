import «.formalsw».tests.py.«local_closure_cells.py.ast»
import FormalSW

namespace tests.py.local_closure_cells
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := LocalClosureCellsAst.module
private def number (value : Int) : Mutable.Value := .scalar (.int value)
private def cellHeap (base : Mutable.Heap) (value : Int) : Mutable.Heap :=
  base ++ [.list [number value]]
private def cellExpr : Expr := .subscript (.name "__formalsw_cell_counter_total") (.constant (.int 0))

private theorem cell_read (base : Mutable.Heap) (value : Int) :
    Mutable.getItem (.ref base.length) (number 0) (cellHeap base value) =
      some (.ok (number value), cellHeap base value) := by
  exact Mutable.getItem_list (cellHeap base value) base.length 0 [number value]
    (by simp [cellHeap]) (by simp)

private theorem cell_store (base : Mutable.Heap) (old value : Int) :
    Mutable.setItem (.ref base.length) (number 0) (number value) (cellHeap base old) =
      some (.ok (.scalar .none), cellHeap base value) := by
  simp [Mutable.setItem, cellHeap, number, Mutable.index, Except.map, List.set_append_right]

/-- Both calls use the same real cell address, and each call updates its current contents. -/
private theorem add_result (amount old : Int) (base : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "__formalsw_local_counter_add" [number amount, .ref base.length]
      (cellHeap base old) (number (old + amount)) (cellHeap base (old + amount)) globals := by
  let args := ((findFunctionIn program.body "__formalsw_local_counter_add").getD ([], [])).1
  let body := ((findFunctionIn program.body "__formalsw_local_counter_add").getD ([], [])).2
  let env := functionEnv args body [number amount, .ref base.length] globals
  have getCell : env "__formalsw_cell_counter_total" = some (.ref base.length) := by cases globals <;> rfl
  have getAmount : env "amount" = some (number amount) := by cases globals <;> rfl
  have update : BlockContinues program env
      [.augAssign cellExpr .add (.name "amount")]
      (cellHeap base old) env (cellHeap base (old + amount)) globals := by
    apply BlockContinues.augItem (target := .ref base.length) (key := number 0)
      (previous := number old) (right := number amount) (updated := number (old + amount))
      (by intros; simp) (Evaluates.lookup getCell) Evaluates.constant (cell_read base old)
      (Evaluates.lookup getAmount) rfl
    exact cell_store base old (old + amount)
  have returned : BlockReturns program env [.return cellExpr]
      (cellHeap base (old + amount)) (number (old + amount)) (cellHeap base (old + amount)) globals :=
    BlockReturns.return_value (Evaluates.subscript (by intros; simp)
      (Evaluates.lookup getCell) Evaluates.constant (cell_read base (old + amount)))
  apply BlockReturns.function rfl rfl
  exact update.returns returned

/-- An arbitrary caller heap survives; the owner sees both nonlocal updates. -/
theorem counter.result (n : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "counter" [number n] heap (number (n + 5)) (cellHeap heap (n + 5)) globals := by
  let args := ((findFunctionIn program.body "counter").getD ([], [])).1
  let body := ((findFunctionIn program.body "counter").getD ([], [])).2
  let env := functionEnv args body [number n] globals
  let allocated := setLocal env "__formalsw_cell_counter_total" (.ref heap.length)
  have getN : env "n" = some (number n) := by cases globals <;> rfl
  have getCell : allocated "__formalsw_cell_counter_total" = some (.ref heap.length) := by simp [allocated, setLocal]
  have allocates : BlockContinues program env
      [.assign [.name "__formalsw_cell_counter_total"] (.list [.name "n"])]
      heap allocated (cellHeap heap n) globals :=
    BlockContinues.assign (Evaluates.list (.cons (Evaluates.lookup getN) .nil))
  have first : Evaluates program allocated
      (.call (.name "__formalsw_local_counter_add") [.constant (.int 2), .name "__formalsw_cell_counter_total"])
      (cellHeap heap n) (number (n + 2)) (cellHeap heap (n + 2)) globals :=
    Evaluates.call (.cons Evaluates.constant (.cons (Evaluates.lookup getCell) .nil)) (add_result 2 n heap globals)
  have second : Evaluates program allocated
      (.call (.name "__formalsw_local_counter_add") [.constant (.int 3), .name "__formalsw_cell_counter_total"])
      (cellHeap heap (n + 2)) (number (n + 2 + 3)) (cellHeap heap (n + 2 + 3)) globals :=
    Evaluates.call (.cons Evaluates.constant (.cons (Evaluates.lookup getCell) .nil)) (add_result 3 (n + 2) heap globals)
  have returned : BlockReturns program allocated [.return cellExpr]
      (cellHeap heap (n + 2 + 3)) (number (n + 2 + 3)) (cellHeap heap (n + 2 + 3)) globals :=
    BlockReturns.return_value (Evaluates.subscript (by intros; simp)
      (Evaluates.lookup getCell) Evaluates.constant (cell_read heap (n + 2 + 3)))
  have completed := allocates.returns ((BlockContinues.discard first).returns ((BlockContinues.discard second).returns returned))
  have arithmetic : n + 2 + 3 = n + 5 := by omega
  rw [arithmetic] at completed
  apply BlockReturns.function rfl rfl
  exact completed

theorem counter.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "counter" [.int n]).Returns :=
  (counter.result n []).scalar_returns (values := [.int n])

theorem counter.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "counter" [.int n]).Supported :=
  (counter.«Returns» n).supported

end tests.py.local_closure_cells
