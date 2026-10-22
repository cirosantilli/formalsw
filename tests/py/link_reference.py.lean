import «.formalsw».tests.py.«link_reference.py.ast»
import FormalSW

namespace tests.py.link_reference
open FormalSW.PyAst FormalSW.PyAst.Calls

theorem double.result (n : Int) :
    ReturnsValue LinkReferenceAst.module "double" [.int n] (.int (n + n)) := by
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.binary (Evaluates.lookup rfl)
    (Evaluates.lookup rfl) (by simp [scalarBinary]))

theorem double.«Returns» (n : Int) :
    (scalarFunction LinkReferenceAst.module "double" [.int n]).Returns :=
  ⟨.int (n + n), .done rfl⟩

end tests.py.link_reference
