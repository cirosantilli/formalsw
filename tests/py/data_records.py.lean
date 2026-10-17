import «.formalsw».tests.py.«data_records.py.ast»
import FormalSW

namespace tests.py.data_records
open FormalSW.PyAst FormalSW.PyAst.HeapCalls

private abbrev program := DataRecordsAst.module
private abbrev origin := (program.classOrigins.lookup "Point").getD ""
private def fields : List Arg :=
  [⟨"x", some (.name "int"), none⟩, ⟨"y", some (.name "int"), none⟩]
private def point (n : Int) : Mutable.Object :=
  .dataInstance origin "Point" true ["x", "y"]
    [("x", .scalar (.int n)), ("y", .scalar (.int (n + 1)))]

private theorem point_result (n : Int) (heap : Mutable.Heap) :
    ReturnsValue program "Point" [.scalar (.int n), .scalar (.int (n + 1))] heap
      (.ref heap.length) (heap ++ [point n]) := by
  exact ReturnsValue.dataclass_constructor (fields := fields) rfl rfl rfl rfl rfl rfl

private theorem point_evaluates (n : Int) (heap : Mutable.Heap) (env : Mutable.Env)
    (lookup : env "n" = some (.scalar (.int n))) :
    Evaluates program env
      (.call (.name "Point") [.name "n", .binOp (.name "n") .add (.constant (.int 1))])
      heap (.ref heap.length) (heap ++ [point n]) := by
  apply Evaluates.call _ (point_result n heap)
  exact .cons (Evaluates.lookup lookup)
    (.cons (Evaluates.binary (Evaluates.lookup lookup) Evaluates.constant rfl) .nil)

theorem read.result (n : Int) :
    ReturnsValue program "read" [.scalar (.int n)] [] (.scalar (.int n)) [point n] := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (point_evaluates n [] _ rfl)
  apply BlockReturns.return_value
  apply Evaluates.field (Evaluates.lookup rfl)
  simp [getAttribute, instanceClass, program, DataRecordsAst.module, Module.findClass,
    Module.findClassBody, findClassBodyIn, point, origin]

theorem equal.result (n : Int) :
    ReturnsValue program "equal" [.scalar (.int n)] [] (.scalar (.bool true)) [point n, point n] := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.compare (point_evaluates n [] _ rfl) (point_evaluates n [point n] _ rfl)
  simp [HeapCalls.compare, point, equalLists, equalElements, scalarCompare, evalCmpOp, List.lookup]
  rfl

theorem read.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "read" [.int n]).Returns := (read.result n).scalar_returns

theorem read.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "read" [.int n]).Supported := (read.«Returns» n).supported

theorem equal.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "equal" [.int n]).Returns := (equal.result n).scalar_returns

theorem equal.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "equal" [.int n]).Supported := (equal.«Returns» n).supported

end tests.py.data_records
