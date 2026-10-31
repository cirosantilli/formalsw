import lang.py.FormalSW.ExtremumBuiltinRelocation
import lang.py.FormalSW.MachineDictionaryMethods

/-! Primitive minima and maxima retain argument effects and exact scalar representatives. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_scalarArgumentCall_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (convert : List Constant → Option (Except ExceptionObject Constant))
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (scalarArgumentCall convert values) stack globals)
      (result physicalAnchors physical (scalarArgumentCall convert (values.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  simpa only [result, run, scalarArgumentCall_result, exceptionArguments_relocates] using
    result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
      ((exceptionArguments values).bind convert) stack globals layout stackInside globalsInside

theorem result_extremumBuiltin_preserves (maximum : Bool) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (primitive (.builtin (if maximum then .max else .min)) values) stack globals)
      (result physicalAnchors physical (primitive (.builtin (if maximum then .max else .min)) (values.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  rw [primitive_extremum_eq, primitive_extremum_eq]
  rcases values with _ | ⟨source, _ | ⟨extra, rest⟩⟩
  case cons.nil =>
    have bounded := valuesInside source (by simp)
    simp only [extremumPrimitive, List.map_cons, List.map_nil, result_bind]
    apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ (List.map (relocateValue rename))
      _ _ globals layout globalsInside
      (fun outcome after executed => extremumPool_heap logical after source bounded outcome executed)
      (extremumPool_relocates logical physical rename layout.runtime source bounded)
    intro items _
    exact result_scalarArgumentCall_preserves logical physical rename logicalAnchors physicalAnchors
      (extremumSequence maximum) items stack globals layout stackInside globalsInside
  all_goals
    exact result_scalarArgumentCall_preserves logical physical rename logicalAnchors physicalAnchors
      (extremumPositional maximum) _ stack globals layout stackInside globalsInside

theorem step_extremumBuiltin_preserves (module : Module) (maximum : Bool)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.builtin (if maximum then .max else .min)) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.builtin (if maximum then .max else .min)) values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation (.builtin (if maximum then .max else .min)) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have raw := result_extremumBuiltin_preserves maximum logical physical rename logicalAnchors physicalAnchors values stack globals
    layout inside.1.2 inside.2 globalsInside
  cases maximum <;> exact raw.protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_extremumBuiltin_preserves (module : Module) (maximum : Bool) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (values : List Mutable.Value) (stack : List Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin logical.length (.running ⟨⟨.operation (.builtin (if maximum then .max else .min)) values, stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running ⟨⟨.operation (.builtin (if maximum then .max else .min)) values, stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running ⟨⟨.operation (.builtin (if maximum then .max else .min)) values, stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running ⟨⟨.operation (.builtin (if maximum then .max else .min)) values, stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_extremumBuiltin_preserves module maximum logical physical rename logicalAnchors physicalAnchors
      values stack globals layout ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
