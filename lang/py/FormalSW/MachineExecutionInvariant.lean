import lang.py.FormalSW.MachineOperationInvariant
import lang.py.FormalSW.MachineBlockInvariant
import lang.py.FormalSW.MachineValueContinuation
import lang.py.FormalSW.MachineExpressionEntry

/-! Every core and iterator transition preserves the execution relation. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem step_complete_preserves (module : Module)
    (source : ∀ statement ∈ module.body, StmtWithin 0 statement)
    (state : State) (physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (globals : Mutable.Globals) (layout : ExecutionLayout state.heap physical rename)
    (inside : StateWithin state) (globalsInside : GlobalsWithin state.heap.length globals) :
    Preserves state.heap physical rename physicalAnchors
      (step module logicalAnchors state globals)
      (step module physicalAnchors (relocateState rename physical state) (relocateGlobals rename globals)) := by
  rcases state with ⟨work, stack, logical⟩
  cases work with
  | sortedLoop => apply step_sortedLoop_preserves <;> assumption
  | extremumLoop => apply step_extremum_loop_preserves <;> assumption
  | dictionary => apply step_dictionary_preserves <;> assumption
  | expr => apply step_expression_preserves <;> assumption
  | block => apply step_block_preserves <;> assumption
  | value => apply step_value_continuation_preserves <;> assumption
  | operation => apply step_operation_preserves <;> assumption
  | startRange => apply step_range_start_preserves <;> assumption

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_complete_preserves (module : Module) (choices : ChoiceSchedule) (state : State)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (heap : StateHeap logical state) (inside : StateWithin logical.length state)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices state globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors state) (relocateGlobals rename globals)) := by
  apply step_preserves module choices state logical physical rename logicalAnchors physicalAnchors globals
    source layout heap inside globalsInside
  intro core resumes same _
  subst state
  have equal : core.core.heap = logical := heap
  subst logical
  exact SetCalls.Relocation.step_preserves_of_heap module choices core physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_complete_preserves module source core.core physical rename logicalAnchors physicalAnchors
      globals layout ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
