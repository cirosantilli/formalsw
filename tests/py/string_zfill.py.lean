import «.formalsw».tests.py.«string_zfill.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.string_zfill
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := StringZfillAst.module

/-- Padding preserves the heap and computes the sign-aware Unicode string operation. -/
theorem fill.result (text : String) (width : Int) (heap : Mutable.Heap) :
    ReturnsValue program "fill" [.scalar (.string text), .scalar (.int width)] heap
      (.scalar (.string (Strings.zfill text width))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.zfill (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil) rfl
  intro name equal
  cases equal
  rfl

theorem fill.«Returns» (text : String) (width : Int) :
    (HeapCalls.scalarFunction program "fill" [.string text, .int width]).Returns :=
  (fill.result text width []).scalar_returns

theorem fill.«Supported» (text : String) (width : Int) :
    (HeapCalls.scalarFunction program "fill" [.string text, .int width]).Supported :=
  (fill.«Returns» text width).supported

end tests.py.string_zfill
