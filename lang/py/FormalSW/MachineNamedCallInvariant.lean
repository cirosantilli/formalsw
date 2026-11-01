import lang.py.FormalSW.MachineConstructorInvariant
import lang.py.FormalSW.MachineLibraryInvariant

/-! Named calls preserve source-function, library and constructor dispatch. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem step_named_call_preserves (module : Module) (name : String)
    (source : ∀ statement ∈ module.body, StmtWithin 0 statement)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.call name) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.call name) values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation (.call name) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases found : findFunctionIn module.body name with
  | some definition =>
    rcases definition with ⟨args, body⟩
    exact step_call_preserves module name args body found
      (findFunctionIn_within 0 module.body name args body source found)
      logical physical rename logicalAnchors physicalAnchors values stack globals layout inside globalsInside
  | none =>
    cases imported : libraryFunction module name with
    | none =>
      exact step_constructor_preserves module name source found imported logical physical rename
        logicalAnchors physicalAnchors values stack globals layout inside globalsInside
    | some function =>
      simpa only [step, relocateState, relocateWork, relocateRuntimeOperation, relocateOperation, found, imported] using
        (result_library_preserves module name logical physical rename logicalAnchors physicalAnchors
          values stack globals layout inside.2 globalsInside).protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_named_call_preserves (module : Module) (choices : ChoiceSchedule) (name : String)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (values : List Mutable.Value) (stack : List HeapCalls.Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin logical.length (.running ⟨⟨.operation (.call name) values, stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running ⟨⟨.operation (.call name) values, stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running ⟨⟨.operation (.call name) values, stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running ⟨⟨.operation (.call name) values, stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_named_call_preserves module name source logical physical rename logicalAnchors physicalAnchors
      values stack globals layout ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
