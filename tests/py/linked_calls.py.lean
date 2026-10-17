import «.formalsw».tests.py.«linked_calls.py.ast»
import tests.py.«link_reference.py»
import FormalSW

namespace tests.py.linked_calls
open FormalSW.PyAst FormalSW.PyAst.Calls

private theorem extends_reference : Extends LinkedCallsAst.module LinkReferenceAst.module := by
  change Extends { body := LinkedCallsAst.module.body.take 2 ++ LinkReferenceAst.module.body } LinkReferenceAst.module
  apply Extends.prepend
  · intro name member
    change name ∈ ["caller", "imported_double"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

theorem caller.result (n : Int) :
    ReturnsValue LinkedCallsAst.module "caller" [.int n] (.int (n + n + 1)) := by
  have reference := (link_reference.double.result n).extend extends_reference
  have alias_result : ReturnsValue LinkedCallsAst.module "imported_double" [.int n] (.int (n + n)) := by
    apply BlockReturns.function rfl rfl
    exact BlockReturns.return_value (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) reference)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.binary (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) alias_result)
    Evaluates.constant (by simp [scalarBinary])

theorem caller.«Returns» (n : Int) :
    (Calls.function LinkedCallsAst.module "caller" [.int n]).Returns := (caller.result n).returns

end tests.py.linked_calls
