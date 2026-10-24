import «.formalsw».tests.py.«binary_format.py.ast»
import lang.py.FormalSW.Calls

namespace tests.py.binary_format
open FormalSW.PyAst
private abbrev program := BinaryFormatAst.module

theorem render.result (n : Int) :
    Calls.ReturnsValue program "render" [.int n] (.string (Strings.binaryRepresentation n)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  exact Calls.Evaluates.builtin (.cons (Calls.Evaluates.lookup rfl) .nil) rfl

theorem render.«Returns» (n : Int) :
    (Calls.function program "render" [.int n]).Returns :=
  (render.result n).returns

theorem render.«Supported» (n : Int) :
    (Calls.function program "render" [.int n]).Supported :=
  (render.«Returns» n).supported

end tests.py.binary_format
