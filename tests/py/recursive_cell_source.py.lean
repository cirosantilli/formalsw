import «.formalsw».tests.py.«recursive_cell_source.py.ast»
import FormalSW

namespace tests.py.recursive_cell_source
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := RecursiveCellSourceAst.module
private def number (value : Int) : Mutable.Value := .scalar (.int value)
private def flag (value : Bool) : Mutable.Value := .scalar (.bool value)
private def cellHeap (base : Mutable.Heap) (value : Int) : Mutable.Heap :=
  base ++ [.list [number value]]
private def cellExpr : Expr := .subscript (.name "__formalsw_cell_count_total") (.constant (.int 0))

private theorem cell_read (base : Mutable.Heap) (value : Int) :
    Mutable.getItem (.ref base.length) (number 0) (cellHeap base value) =
      some (.ok (number value), cellHeap base value) := by
  exact Mutable.getItem_list (cellHeap base value) base.length 0 [number value]
    (by simp [cellHeap]) (by simp)

private theorem cell_store (base : Mutable.Heap) (old value : Int) :
    Mutable.setItem (.ref base.length) (number 0) (number value) (cellHeap base old) =
      some (.ok (.scalar .none), cellHeap base value) := by
  simp [Mutable.setItem, cellHeap, number, Mutable.index, Except.map, List.set_append_right]

private theorem tick_source :
    executableBody ((findFunctionIn program.body "__formalsw_local_count_tick").getD ([], [])).2 =
      [.augAssign cellExpr .add (.constant (.int 1)), .return cellExpr] := rfl

private theorem down_source :
    executableBody ((findFunctionIn program.body "__formalsw_local_count_down").getD ([], [])).2 =
      [.ifThen (.compare (.name "k") [(.ltE, .constant (.int 0))]) [.return cellExpr] [],
       .expr (.call (.name "__formalsw_local_count_tick") [.name "__formalsw_cell_count_total"]),
       .return (.call (.name "__formalsw_local_count_down")
         [.binOp (.name "k") .sub (.constant (.int 1)), .name "__formalsw_cell_count_total"])] := rfl

/-- The sibling writer updates the one shared lexical cell, retaining the caller prefix. -/
private theorem tick_result (old : Int) (base : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "__formalsw_local_count_tick" [.ref base.length]
      (cellHeap base old) (number (old + 1)) (cellHeap base (old + 1)) globals := by
  let args := ((findFunctionIn program.body "__formalsw_local_count_tick").getD ([], [])).1
  let body := ((findFunctionIn program.body "__formalsw_local_count_tick").getD ([], [])).2
  let env := functionEnv args body [.ref base.length] globals
  have getCell : env "__formalsw_cell_count_total" = some (.ref base.length) := by cases globals <;> rfl
  have update : BlockContinues program env [.augAssign cellExpr .add (.constant (.int 1))]
      (cellHeap base old) env (cellHeap base (old + 1)) globals := by
    apply BlockContinues.augItem (target := .ref base.length) (key := number 0)
      (previous := number old) (right := number 1) (updated := number (old + 1))
      (by intros; simp) (Evaluates.lookup getCell) Evaluates.constant (cell_read base old)
      Evaluates.constant rfl
    exact cell_store base old (old + 1)
  have returned : BlockReturns program env [.return cellExpr]
      (cellHeap base (old + 1)) (number (old + 1)) (cellHeap base (old + 1)) globals :=
    BlockReturns.return_value (Evaluates.subscript (by intros; simp)
      (Evaluates.lookup getCell) Evaluates.constant (cell_read base (old + 1)))
  apply BlockReturns.function rfl rfl
  exact update.returns returned

/-- Every positive recursive source call consumes one unit of n.toNat. The shared
cell is threaded unchanged as a reference through both sibling and recursive calls. -/
theorem down_result (n old : Int) (base : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "__formalsw_local_count_down" [number n, .ref base.length]
      (cellHeap base old) (number (old + (n.toNat : Int))) (cellHeap base (old + (n.toNat : Int))) globals := by
  generalize fuelEq : n.toNat = fuel
  induction fuel generalizing n old with
  | zero =>
      have nonpositive : n ≤ 0 := by omega
      let args := ((findFunctionIn program.body "__formalsw_local_count_down").getD ([], [])).1
      let body := ((findFunctionIn program.body "__formalsw_local_count_down").getD ([], [])).2
      let env := functionEnv args body [number n, .ref base.length] globals
      have getK : env "k" = some (number n) := by cases globals <;> rfl
      have getCell : env "__formalsw_cell_count_total" = some (.ref base.length) := by cases globals <;> rfl
      have test : Evaluates program env (.compare (.name "k") [(.ltE, .constant (.int 0))])
          (cellHeap base old) (flag true) (cellHeap base old) globals := by
        apply Evaluates.compare (Evaluates.lookup getK) Evaluates.constant
        simp [HeapCalls.compare, number, flag, scalarCompare, evalCmpOp, nonpositive]
      have returns : ReturnsValue program "__formalsw_local_count_down" [number n, .ref base.length]
          (cellHeap base old) (number old) (cellHeap base old) globals := by
        apply BlockReturns.function rfl rfl
        apply BlockReturns.branch (flag := true) test rfl
        exact BlockReturns.return_value (Evaluates.subscript (by intros; simp)
          (Evaluates.lookup getCell) Evaluates.constant (cell_read base old))
      simpa using returns
  | succ fuel ih =>
      have positive : 0 < n := by omega
      have nextFuel : (n - 1).toNat = fuel := by omega
      let args := ((findFunctionIn program.body "__formalsw_local_count_down").getD ([], [])).1
      let body := ((findFunctionIn program.body "__formalsw_local_count_down").getD ([], [])).2
      let env := functionEnv args body [number n, .ref base.length] globals
      have getK : env "k" = some (number n) := by cases globals <;> rfl
      have getCell : env "__formalsw_cell_count_total" = some (.ref base.length) := by cases globals <;> rfl
      have test : Evaluates program env (.compare (.name "k") [(.ltE, .constant (.int 0))])
          (cellHeap base old) (flag false) (cellHeap base old) globals := by
        apply Evaluates.compare (Evaluates.lookup getK) Evaluates.constant
        simp [HeapCalls.compare, number, flag, scalarCompare, evalCmpOp, show ¬n ≤ 0 by omega]
      have sibling : Evaluates program env
          (.call (.name "__formalsw_local_count_tick") [.name "__formalsw_cell_count_total"])
          (cellHeap base old) (number (old + 1)) (cellHeap base (old + 1)) globals :=
        Evaluates.call (.cons (Evaluates.lookup getCell) .nil) (tick_result old base globals)
      have decrement : Evaluates program env (.binOp (.name "k") .sub (.constant (.int 1)))
          (cellHeap base (old + 1)) (number (n - 1)) (cellHeap base (old + 1)) globals :=
        Evaluates.binary (Evaluates.lookup getK) Evaluates.constant rfl
      have recursive := ih (n - 1) (old + 1) nextFuel
      have called : Evaluates program env
          (.call (.name "__formalsw_local_count_down")
            [.binOp (.name "k") .sub (.constant (.int 1)), .name "__formalsw_cell_count_total"])
          (cellHeap base (old + 1)) (number (old + 1 + (fuel : Int)))
          (cellHeap base (old + 1 + (fuel : Int))) globals :=
        Evaluates.call (.cons decrement (.cons (Evaluates.lookup getCell) .nil)) recursive
      have returns : ReturnsValue program "__formalsw_local_count_down" [number n, .ref base.length]
          (cellHeap base old) (number (old + 1 + (fuel : Int)))
          (cellHeap base (old + 1 + (fuel : Int))) globals := by
        apply BlockReturns.function rfl rfl
        apply BlockReturns.branch (flag := false) test rfl
        exact BlockReturns.discard sibling (BlockReturns.return_value called)
      have arithmetic : old + 1 + (fuel : Int) = old + ((fuel + 1 : Nat) : Int) := by omega
      simpa only [arithmetic] using returns

/-- The owner observes all recursive nonlocal writes, for every signed input. -/
theorem count.result (n : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "count" [number n] heap (number n.toNat) (cellHeap heap n.toNat) globals := by
  let args := ((findFunctionIn program.body "count").getD ([], [])).1
  let body := ((findFunctionIn program.body "count").getD ([], [])).2
  let env := functionEnv args body [number n] globals
  let allocated := setLocal env "__formalsw_cell_count_total" (.ref heap.length)
  have getN : allocated "n" = some (number n) := by cases globals <;> rfl
  have getCell : allocated "__formalsw_cell_count_total" = some (.ref heap.length) := by simp [allocated, setLocal]
  have allocates : BlockContinues program env
      [.assign [.name "__formalsw_cell_count_total"] (.list [.constant (.int 0)])]
      heap allocated (cellHeap heap 0) globals :=
    BlockContinues.assign (Evaluates.list (.cons Evaluates.constant .nil))
  have calls : Evaluates program allocated
      (.call (.name "__formalsw_local_count_down") [.name "n", .name "__formalsw_cell_count_total"])
      (cellHeap heap 0) (number n.toNat) (cellHeap heap n.toNat) globals := by
    simpa only [Int.zero_add] using
      Evaluates.call (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getCell) .nil)) (down_result n 0 heap globals)
  have returned : BlockReturns program allocated [.return cellExpr]
      (cellHeap heap n.toNat) (number n.toNat) (cellHeap heap n.toNat) globals :=
    BlockReturns.return_value (Evaluates.subscript (by intros; simp)
      (Evaluates.lookup getCell) Evaluates.constant (cell_read heap n.toNat))
  apply BlockReturns.function rfl rfl
  exact allocates.returns ((BlockContinues.discard calls).returns returned)

theorem count.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "count" [.int n]).Returns :=
  (count.result n []).scalar_returns (values := [.int n])

theorem count.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "count" [.int n]).Supported :=
  (count.«Returns» n).supported

end tests.py.recursive_cell_source
