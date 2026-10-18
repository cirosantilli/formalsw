import «.formalsw».tests.py.«math_comb.py.ast»
import FormalSW

namespace tests.py.math_comb
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := MathCombAst.module

theorem choose.result (n k : Nat) :
    ReturnsValue program "choose" [.int n, .int k] (.int (Math.comb n k)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.library_call (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) rfl
  exact congrArg some (Math.combCall_naturals n k)

theorem qualified.result (n k : Nat) :
    ReturnsValue program "qualified" [.int n, .int k] (.int (Math.comb n k)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.qualified_call
  apply Evaluates.library_call (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) rfl
  exact congrArg some (Math.combCall_naturals n k)

theorem choose.«Returns» (n k : Int)
    (hn : Condition program (fun name => if name = "n" then some (.int n) else none)
      MathCombAst.requires_choose_0)
    (hk : Condition program (fun name => if name = "k" then some (.int k) else none)
      MathCombAst.requires_choose_1) :
    (function program "choose" [.int n, .int k]).Returns := by
  have nonnegN : 0 ≤ n := by simpa [evalCmpOp] using Evaluates.condition_int_compare hn rfl
  have nonnegK : 0 ≤ k := by simpa [evalCmpOp] using Evaluates.condition_int_compare hk rfl
  simpa [Int.toNat_of_nonneg nonnegN, Int.toNat_of_nonneg nonnegK] using (choose.result n.toNat k.toNat).returns

theorem qualified.«Equiv(choose)» (n k : Int)
    (hn : Condition program (fun name => if name = "n" then some (.int n) else none)
      MathCombAst.requires_qualified_0)
    (hk : Condition program (fun name => if name = "k" then some (.int k) else none)
      MathCombAst.requires_qualified_1) :
    (function program "qualified" [.int n, .int k]).Equiv
      (function program "choose" [.int n, .int k]) := by
  have nonnegN : 0 ≤ n := by simpa [evalCmpOp] using Evaluates.condition_int_compare hn rfl
  have nonnegK : 0 ≤ k := by simpa [evalCmpOp] using Evaluates.condition_int_compare hk rfl
  have left := qualified.result n.toNat k.toNat
  have right := choose.result n.toNat k.toNat
  simpa [Int.toNat_of_nonneg nonnegN, Int.toNat_of_nonneg nonnegK] using
    left.equiv right

end tests.py.math_comb
