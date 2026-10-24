import «.formalsw».tests.py.«string_membership.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.string_membership
open FormalSW.PyAst HeapCalls
private abbrev program := StringMembershipAst.module

theorem present.result (text substring : String) (heap : Mutable.Heap) :
    ReturnsValue program "present" [.scalar (.string text), .scalar (.string substring)] heap
      (.scalar (.bool (Strings.contains text substring))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.membership (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil))
    (membership_string heap text substring false)

theorem present.«Returns» (text substring : String) :
    (HeapCalls.scalarFunction program "present" [.string text, .string substring]).Returns :=
  (present.result text substring []).scalar_returns

theorem present.«Supported» (text substring : String) :
    (HeapCalls.scalarFunction program "present" [.string text, .string substring]).Supported :=
  (present.«Returns» text substring).supported

theorem absent.result (text substring : String) (heap : Mutable.Heap) :
    ReturnsValue program "absent" [.scalar (.string text), .scalar (.string substring)] heap
      (.scalar (.bool (!Strings.contains text substring))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.membership (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil))
    (membership_string heap text substring true)

theorem absent.«Returns» (text substring : String) :
    (HeapCalls.scalarFunction program "absent" [.string text, .string substring]).Returns :=
  (absent.result text substring []).scalar_returns

theorem absent.«Supported» (text substring : String) :
    (HeapCalls.scalarFunction program "absent" [.string text, .string substring]).Supported :=
  (absent.«Returns» text substring).supported

end tests.py.string_membership
