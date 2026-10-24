import «.formalsw».tests.py.«bitwise_or_shift.py.ast»
import lang.py.FormalSW.Calls

namespace tests.py.bitwise_or_shift
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := BitwiseOrShiftAst.module

theorem merge.result (a b : Int) :
    ReturnsValue program "merge" [.int a, .int b] (.int (integerBitOr a b)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl)
    (by simp [scalarBinary, scalarBitOr])

theorem merge.«Returns» (a b : Int) : (function program "merge" [.int a, .int b]).Returns :=
  (merge.result a b).returns

theorem merge.«Supported» (a b : Int) : (function program "merge" [.int a, .int b]).Supported :=
  (merge.«Returns» a b).supported

theorem either.result (a b : Bool) :
    ReturnsValue program "either" [.bool a, .bool b] (.bool (a || b)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl) rfl

theorem either.«Returns» (a b : Bool) : (function program "either" [.bool a, .bool b]).Returns :=
  (either.result a b).returns

theorem either.«Supported» (a b : Bool) : (function program "either" [.bool a, .bool b]).Supported :=
  (either.«Returns» a b).supported

theorem shift.result (a count : Int) (nonnegative : 0 ≤ count) :
    ReturnsValue program "shift" [.int a, .int count] (.int (integerShiftLeft a count.toNat)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl)
    (by simp [scalarBinary, scalarShiftLeft, Int.not_lt.mpr nonnegative])

theorem shift.«Returns» (a count : Int) (condition : Calls.Condition program
    (fun name => if name = "count" then some (.int count) else none) BitwiseOrShiftAst.requires_shift_0) :
    (function program "shift" [.int a, .int count]).Returns := by
  have nonnegative : 0 ≤ count := by
    simpa [evalCmpOp] using Evaluates.condition_int_compare condition rfl
  exact (shift.result a count nonnegative).returns

theorem shift.«Supported» (a count : Int) (condition : Calls.Condition program
    (fun name => if name = "count" then some (.int count) else none) BitwiseOrShiftAst.requires_shift_0) :
    (function program "shift" [.int a, .int count]).Supported :=
  (shift.«Returns» a count condition).supported

end tests.py.bitwise_or_shift
