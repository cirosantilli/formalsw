import lang.py.FormalSW.HeapqBuiltinRelocation
import lang.py.FormalSW.MachineSortedBuiltins

/-! Heap operations retain argument effects and saved callers through successful or failed sifts. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- Matching mutations preserve the full machine result, including unsupported operations. -/
theorem result_mutation_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (action otherAction : Mutable.Eval Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (related : MutationRelocates logical physical rename (relocateValue rename) action otherAction)
    (bounded : ∀ value after, action logical = some (.ok value, after) → value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical action stack globals)
      (result physicalAnchors physical otherAction (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  cases executed : action logical with
  | none =>
    have other := related.unsupported_iff.mp executed
    apply Preserves.unchanged layout <;>
      simp [result, run, executed, other, StepHeap, StepWithin, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    obtain ⟨other, paired, retained, leftLength, rightLength⟩ := related.completed outcome after executed
    apply result_preserves logical physical after other rename rename logicalAnchors physicalAnchors _ _ stack globals outcome
      (fun _ _ => rfl) (Nat.le_of_eq leftLength.symm) (Nat.le_of_eq rightLength.symm)
      retained stackInside globalsInside _ executed paired
    intro value equal
    subst outcome
    simpa only [leftLength] using bounded value after executed

inductive HeapqOperation : Operation → Prop
  | heapify : HeapqOperation (.builtin .heapqHeapify)
  | push : HeapqOperation (.builtin .heapqPush)
  | pop : HeapqOperation (.builtin .heapqPop)

theorem heapq_primitive_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (operation : Operation) (covered : HeapqOperation operation)
    (values : List Value) (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    MutationRelocates logical physical rename (relocateValue rename) (primitive operation values)
      (primitive operation (values.map (relocateValue rename))) := by
  cases covered with
  | heapify => exact Heapq.Relocation.heapify_relocates layout values inside
  | push => exact Heapq.Relocation.heappush_relocates layout values inside
  | pop => exact Heapq.Relocation.heappop_relocates layout values inside

theorem heapq_primitive_bounded (heap after : Mutable.Heap) (closed : Closed heap)
    (operation : Operation) (covered : HeapqOperation operation) (values : List Value) (returned : Value)
    (executed : primitive operation values heap = some (.ok returned, after)) : returned.edge.Within heap.length := by
  cases covered with
  | heapify =>
    rw [Heapq.Relocation.heapify_returns_none heap after values returned executed]
    trivial
  | push =>
    rw [Heapq.Relocation.heappush_returns_none heap after values returned executed]
    trivial
  | pop => exact Heapq.Relocation.heappop_return_bounded heap after closed values returned executed

theorem result_heapqBuiltin_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (operation : Operation) (covered : HeapqOperation operation)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (primitive operation values) stack globals)
      (result physicalAnchors physical (primitive operation (values.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  exact result_mutation_preserves logical physical rename logicalAnchors physicalAnchors _ _ stack globals layout
    (heapq_primitive_relocates logical physical rename layout operation covered values valuesInside)
    (fun value after executed => heapq_primitive_bounded logical after layout.closed operation covered values value executed)
    stackInside globalsInside

theorem step_heapqBuiltin_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (operation : Operation) (covered : HeapqOperation operation)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation operation values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation operation values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation operation values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have raw := result_heapqBuiltin_preserves logical physical rename logicalAnchors physicalAnchors operation covered
    values stack globals layout inside.1.2 inside.2 globalsInside
  cases covered <;> exact raw.protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_heapqBuiltin_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (operation : Operation) (covered : HeapqOperation operation) (values : List Mutable.Value)
    (stack : List HeapCalls.Frame) (resumes : List Resume) (globals : Mutable.Globals)
    (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin logical.length (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_heapqBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      operation covered values stack globals layout ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
