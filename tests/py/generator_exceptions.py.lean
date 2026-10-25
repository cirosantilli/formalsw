import «.formalsw».tests.py.«generator_exceptions.py.ast»
import lang.py.FormalSW.HeapCalls
import lang.py.FormalSW.MemoCalls

namespace tests.py.generator_exceptions
open FormalSW.PyAst
private abbrev program := GeneratorExceptionsAst.module
set_option maxRecDepth 8192

theorem wrapped.result (n : Int) :
    Finishes (Calls.function program "wrapped" [.int n]).step
      (Calls.function program "wrapped" [.int n]).initial
      (.error ⟨"RuntimeError", []⟩) :=
  Execution.finishes_of_observe (fuel := 100) rfl

theorem first_iterable.result (n : Int) :
    Finishes (Calls.function program "first_iterable" [.int n]).step
      (Calls.function program "first_iterable" [.int n]).initial
      (.error ⟨"StopIteration", [.int n]⟩) :=
  Execution.finishes_of_observe (fuel := 100) rfl

theorem heap_wrapped.result (n : Int) :
    Finishes (HeapCalls.scalarFunction program "heap_wrapped" [.int n]).step
      (HeapCalls.scalarFunction program "heap_wrapped" [.int n]).initial
      (.error ⟨"RuntimeError", []⟩) :=
  Execution.finishes_of_observe (fuel := 100) rfl

theorem memo_wrapped.result (n : Int) :
    Finishes (MemoCalls.sourceFunction program "memo_wrapped" [.int n]).step
      (MemoCalls.sourceFunction program "memo_wrapped" [.int n]).initial
      (.error ⟨"RuntimeError", []⟩) :=
  Execution.finishes_of_observe (fuel := 100) rfl

theorem wrapped.«Throws» : ∃ n : Int, (Calls.function program "wrapped" [.int n]).Throws :=
  ⟨0, _, wrapped.result 0⟩

theorem first_iterable.«Throws» : ∃ n : Int, (Calls.function program "first_iterable" [.int n]).Throws :=
  ⟨0, _, first_iterable.result 0⟩

theorem heap_wrapped.«Throws» : ∃ n : Int, (HeapCalls.scalarFunction program "heap_wrapped" [.int n]).Throws :=
  ⟨0, _, heap_wrapped.result 0⟩

theorem heap_wrapped.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "heap_wrapped" [.int n]).Supported :=
  Execution.supported_of_finishes (heap_wrapped.result n)

theorem memo_wrapped.«Throws» : ∃ n : Int, (MemoCalls.sourceFunction program "memo_wrapped" [.int n]).Throws :=
  ⟨0, _, memo_wrapped.result 0⟩

theorem memo_wrapped.«Supported» (n : Int) :
    (MemoCalls.sourceFunction program "memo_wrapped" [.int n]).Supported :=
  Execution.supported_of_finishes (memo_wrapped.result n)

end tests.py.generator_exceptions
