import «.formalsw».tests.py.«formatted_raise.py.ast»
import FormalSW

namespace tests.py.formatted_raise
open FormalSW.PyAst
private abbrev program := FormattedRaiseAst.module

theorem describe.result (n : Int) :
    Finishes (Calls.function program "describe" [.int n]).step
      (Calls.function program "describe" [.int n]).initial
      (.ok (.string ("value " ++ toString n))) := by
  repeat first | exact .done rfl | refine .next rfl ?_

theorem describe.«Returns» (n : Int) :
    (Calls.function program "describe" [.int n]).Returns :=
  ⟨_, describe.result n⟩

theorem describe.«ReturnType» (n : Int) :
    (Calls.function program "describe" [.int n]).ReturnType "str" :=
  .inr ⟨_, describe.result n, rfl⟩

theorem reject.result (n : Int) :
    Finishes (Calls.function program "reject" [.int n]).step
      (Calls.function program "reject" [.int n]).initial
      (.error ⟨"ValueError", [.string ("value " ++ toString n)]⟩) := by
  repeat first | exact .done rfl | refine .next rfl ?_

theorem reject.«Halts» (n : Int) :
    (Calls.function program "reject" [.int n]).Halts :=
  ⟨_, reject.result n⟩

theorem reject.«Throws» : ∃ n : Int,
    (Calls.function program "reject" [.int n]).Throws :=
  ⟨0, _, reject.result 0⟩

end tests.py.formatted_raise
