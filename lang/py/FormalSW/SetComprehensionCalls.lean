import lang.py.FormalSW.SetCalls

/-! Source rules enter an arbitrary-order set traversal with a fresh comprehension collector. -/
namespace FormalSW.PyAst.SetCalls
open HeapCalls
set_option Elab.async false

/-- Capturing a named set starts the iterator without consuming a traversal choice. -/
theorem list_comp_set_start (module : Module) (env : HeapCalls.Env) (heap : Mutable.Heap)
    (source name : String) (address : Nat) (items : List Constant)
    (lookup : env source = some (.ref address)) (found : heap[address]? = some (.set items))
    (element : Expr) (filters : List Expr) (generators : List (String × Expr × List Expr))
    (choices : ChoiceSchedule) (anchors : Nat) (stack : List HeapCalls.Frame) (used : Nat) :
    Reaches choices module anchors
      ⟨⟨.expr (.listComp element ((name, .name source, filters) :: generators)) env,
        stack, heap⟩, used⟩
      ⟨⟨.block [.setStepLoop name address items items
          (comprehensionFilters filters (comprehensionBody heap.length element generators)) []]
        (comprehensionEnv env ((name, .name source, filters) :: generators)),
        .comprehensionResult heap.length :: stack, heap ++ [.list []]⟩, used⟩ := by
  have arguments : HeapCalls.Evaluates.Arguments module env [.name source] heap
      [.ref address] heap := .cons (HeapCalls.Evaluates.lookup lookup) .nil
  have entry : HeapCalls.Reaches module anchors
      ⟨.expr (.listComp element ((name, .name source, filters) :: generators)) env, stack, heap⟩
      ⟨.operation (.comprehension element ((name, .name source, filters) :: generators)
        (comprehensionEnv env ((name, .name source, filters) :: generators))) [.ref address],
        stack, heap⟩ :=
    .next rfl (HeapCalls.Evaluates.arguments_reach arguments _ [] anchors stack)
  apply (Reaches.of_heap entry choices used).trans
  exact .next (by
    simp [step, HeapCalls.step, HeapCalls.comprehensionStart, run, Mutable.sequence, found,
      Mutable.unsupported, iteratorStep, comprehensionStart,
      comprehensionTargetName, comprehensionTargetBody]) .refl

end FormalSW.PyAst.SetCalls
