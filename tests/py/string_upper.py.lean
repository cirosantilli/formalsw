import «.formalsw».tests.py.«string_upper.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.string_upper
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := StringUpperAst.module

/-- Arbitrary ASCII inputs retain the caller heap and compute the exact uppercase mapping. -/
theorem convert.result (text : String) (ascii : Strings.isAscii text = true) (heap : Mutable.Heap) :
    ReturnsValue program "convert" [.scalar (.string text)] heap
      (.scalar (.string (Strings.asciiUpper text))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.upper_ascii (Evaluates.lookup rfl) ascii
  intro name equal
  cases equal
  rfl

theorem uppercase_ascii.«Returns» :
    (HeapCalls.scalarFunction program "uppercase_ascii" []).Returns := by
  apply ReturnsValue.scalar_returns (value := .string "ABCXYZ09!") (heap := [])
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.call (.cons Evaluates.constant .nil) (convert.result "abcXYZ09!" (by decide) [])

theorem uppercase_ascii.«Supported» :
    (HeapCalls.scalarFunction program "uppercase_ascii" []).Supported :=
  uppercase_ascii.«Returns».supported

end tests.py.string_upper
