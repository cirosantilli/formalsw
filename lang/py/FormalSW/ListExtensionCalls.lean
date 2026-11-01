import lang.py.FormalSW.HeapCalls

/-! Shallow list extension retains element aliases and snapshots self-extension. -/
namespace FormalSW.PyAst.HeapCalls
set_option Elab.async false

theorem extendList_list (heap : Heap) (address source : Nat) (items additional : List Value)
    (destination : heap[address]? = some (.list items))
    (input : heap[source]? = some (.list additional)) :
    primitive (.extendList address) [.ref source] heap =
      some (.ok (.scalar .none), heap.set address (.list (items ++ additional))) := by
  simp [primitive, extendList, destination, input, Except.map]

theorem extendList_tuple (heap : Heap) (address source : Nat) (items additional : List Value)
    (destination : heap[address]? = some (.list items))
    (input : heap[source]? = some (.tuple additional)) :
    primitive (.extendList address) [.ref source] heap =
      some (.ok (.scalar .none), heap.set address (.list (items ++ additional))) := by
  simp [primitive, extendList, destination, input, Except.map]

/-- Argument effects occur after method binding and before the destination is read. -/
theorem Evaluates.extendList {globals : Mutable.Globals}
    (receiver : Evaluates (globals := globals) module env base heap (.ref address) middle)
    (found : middle[address]? = some (.list items))
    (arguments : Evaluates.Arguments (globals := globals) module env expressions middle values afterArguments)
    (operation : primitive (.extendList address) values afterArguments = some (.ok value, finalHeap))
    (localName : ∀ name, base = .name name → (env name).isSome = true) :
    Evaluates (globals := globals) module env (.call (.attribute base "extend") expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr base env, .methodReceiver "extend" expressions env :: stack, heap⟩)
    (by cases base <;> simp_all [step])
  apply (receiver anchors _).trans
  apply Reaches.next (following := argumentsState (.extendList address) env [] expressions stack middle)
    (by simp [step, run, bindMethod, found])
  apply (Evaluates.arguments_reach arguments (.extendList address) [] anchors stack).trans
  exact .next (by simp [step, result, run, operation]) .refl

end FormalSW.PyAst.HeapCalls
