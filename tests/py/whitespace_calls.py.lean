import «.formalsw».tests.py.«whitespace_calls.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.whitespace_calls
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := WhitespaceCallsAst.module
private abbrev textValue (text : String) : Mutable.Value := .scalar (.string text)
private def wordsValue (text : String) : Mutable.Object := .list ((Strings.splitWhitespace text).map textValue)

/-- Trimming reads an arbitrary Unicode string without changing the caller's heap. -/
theorem trimmed.result (text : String) (heap : Mutable.Heap) :
    ReturnsValue program "trimmed" [textValue text] heap (textValue (Strings.stripWhitespace text)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.strip (Evaluates.lookup rfl) (by intro name equal; cases equal; rfl)

theorem trimmed.«Returns» (text : String) :
    (HeapCalls.scalarFunction program "trimmed" [.string text]).Returns := (trimmed.result text []).scalar_returns

theorem trimmed.«Supported» (text : String) :
    (HeapCalls.scalarFunction program "trimmed" [.string text]).Supported := (trimmed.«Returns» text).supported

/-- Splitting allocates one fresh list and preserves every object that existed before the call. -/
theorem words.result (text : String) (heap : Mutable.Heap) :
    ReturnsValue program "words" [textValue text] heap (.ref heap.length) (heap ++ [wordsValue text]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.split_whitespace (Evaluates.lookup rfl) (by intro name equal; cases equal; rfl)

theorem words.«Returns» (text : String) :
    (HeapCalls.call program "words" [textValue text] []).Returns := (words.result text []).returns

theorem words.«Supported» (text : String) :
    (HeapCalls.call program "words" [textValue text] []).Supported := (words.«Returns» text).supported

/-- Both chained receivers execute through the ordinary method-binding rules. -/
theorem normalized.result (text : String) (heap : Mutable.Heap) :
    ReturnsValue program "normalized" [textValue text] heap (.ref heap.length) (heap ++ [wordsValue (Strings.stripWhitespace text)]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.split_whitespace
  · exact Evaluates.strip (Evaluates.lookup rfl) (by intro name equal; cases equal; rfl)
  · intro name impossible
    cases impossible

theorem normalized.«Returns» (text : String) :
    (HeapCalls.call program "normalized" [textValue text] []).Returns := (normalized.result text []).returns

theorem normalized.«Supported» (text : String) :
    (HeapCalls.call program "normalized" [textValue text] []).Supported := (normalized.«Returns» text).supported

end tests.py.whitespace_calls
