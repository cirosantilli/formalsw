import «.formalsw».tests.py.«classes.py.ast»
import FormalSW

namespace tests.py.classes
open FormalSW.PyAst

set_option maxRecDepth 8192 in
private theorem shared.run (n : Int) :
    Finishes (HeapCalls.scalarFunction ClassesAst.module "shared" [.int n]).step
      (HeapCalls.scalarFunction ClassesAst.module "shared" [.int n]).initial
      (.ok (.int (n + 2 + (n + 2)))) :=
  Execution.finishes_of_observe (fuel := 200) rfl

theorem shared.«Returns» (n : Int) :
    (HeapCalls.scalarFunction ClassesAst.module "shared" [.int n]).Returns :=
  ⟨_, shared.run n⟩

theorem shared.«Supported» (n : Int) :
    (HeapCalls.scalarFunction ClassesAst.module "shared" [.int n]).Supported :=
  Execution.supported_of_finishes (shared.run n)

end tests.py.classes
