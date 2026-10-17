import FormalSW

open FormalSW.PyAst

namespace ObjectEquivalenceExamples

-- The same one-node cycle, with a different address and an unreachable object.
def leftCycle : Graph.Heap :=
  ⟨[.ref 0], [⟨.object 7, ["value", "next"], [.scalar (.int 7), .ref 0]⟩]⟩

def rightCycle : Graph.Heap :=
  ⟨[.ref 1], [⟨.list, [], []⟩,
    ⟨.object 7, ["value", "next"], [.scalar (.int 7), .ref 1]⟩]⟩

def corruptCycle : Graph.Heap :=
  ⟨[.ref 0], [⟨.object 7, ["value", "next"], [.scalar (.int 8), .ref 0]⟩]⟩

theorem renamed_allocations : Graph.Equivalent leftCycle.encode rightCycle.encode := by
  apply Graph.equivalent_of_observe (fuel := 500)
  native_decide

theorem changed_attribute : ¬ Graph.Equivalent leftCycle.encode corruptCycle.encode := by
  apply Graph.not_equivalent_of_observe (fuel := 500)
  native_decide

-- Roots are [return value, caller's argument]; one result aliases the input.
def returnedInput : Graph.Heap :=
  ⟨[.ref 0, .ref 0], [⟨.list, [], [.scalar (.int 1)]⟩]⟩

def returnedCopy : Graph.Heap :=
  ⟨[.ref 0, .ref 1], [⟨.list, [], [.scalar (.int 1)]⟩,
    ⟨.list, [], [.scalar (.int 1)]⟩]⟩

theorem copying_changes_aliases : ¬ Graph.Equivalent returnedInput.encode returnedCopy.encode := by
  apply Graph.not_equivalent_of_observe (fuel := 500)
  native_decide

theorem result_equivalence :
    Graph.Equiv (Execution.pure leftCycle.encode) (Execution.pure rightCycle.encode) := by
  constructor
  · intro outcome finished
    have same := finished.unique (Finishes.done rfl)
    subst outcome
    exact ⟨_, .done rfl, renamed_allocations⟩
  · intro outcome finished
    have same := finished.unique (Finishes.done rfl)
    subst outcome
    exact ⟨_, .done rfl, renamed_allocations⟩

-- A symbolic, kernel-checked fast path: no graph traversal or native_decide.
example (a b : Int) : Graph.Equivalent (.scalar (.int a)) (.scalar (.int b)) ↔ a = b :=
  Graph.equivalent_int a b

-- The generic interpreter also runs other Python definitions unchanged.
def countDown : Module := python_data% r#"
def count_down(n):
    while n > 0:
        n = n - 1
    return n == 0
"#

example : Graph.observedBool ((dataFunction countDown "count_down" [.scalar (.int 12)]).observe 40)
    = some true := by native_decide

end ObjectEquivalenceExamples
