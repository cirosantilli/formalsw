import lang.py.FormalSW.MachineExpressionInvariant

/-! Builtin length reads retain the execution invariant after argument effects. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- Length reads return scalars or errors without mutating the heap. -/
theorem length_scalar_result (heap : Mutable.Heap) (value : Value) :
    ∃ outcome : Option (Except ExceptionObject Constant),
      Mutable.length value heap = scalarResult outcome heap := by
  cases value with
  | scalar scalar =>
    refine ⟨some (Calls.length scalar), ?_⟩
    cases scalar <;> rfl
  | ref address =>
    cases found : heap[address]? with
    | none => exact ⟨none, by simp [Mutable.length, found, scalarResult, Mutable.unsupported]⟩
    | some object =>
      cases object with
      | list items | tuple items | bytearray items | set items | keySet items | dict items | keyDict items =>
        exact ⟨some (.ok (.int items.length)), by simp [Mutable.length, found, scalarResult]⟩
      | «instance» origin name fields | dataInstance origin name frozen declared fields =>
        exact ⟨some (.error ⟨"TypeError", []⟩), by simp [Mutable.length, found, scalarResult, Mutable.error]⟩

theorem length_effect (heap after : Mutable.Heap) (value : Value)
    (outcome : Except ExceptionObject Value)
    (executed : Mutable.length value heap = some (outcome, after)) :
    after = heap ∧ ∀ returned, outcome = .ok returned → ∃ scalar, returned = .scalar scalar := by
  obtain ⟨result, equation⟩ := length_scalar_result heap value
  rw [equation] at executed
  exact scalarResult_effect heap after result outcome executed

/-- This rule includes modeled errors and unsupported outcomes, without a completion premise. -/
theorem step_length_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (valueInside : value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.builtin .len) [value], stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.builtin .len) [value], stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have raw := result_readonly_preserves logical physical rename logicalAnchors physicalAnchors
    (Mutable.length value) (Mutable.length (relocateValue rename value)) stack globals layout stackInside globalsInside (by
      intro outcome after executed
      obtain ⟨same, scalar⟩ := length_effect logical after value outcome executed
      refine ⟨same, ?_⟩
      intro returned success
      obtain ⟨constant, rfl⟩ := scalar returned success
      trivial) (layout.runtime.length value valueInside)
  exact raw.protectGenerator stack stackInside

/-- Other arities retain the interpreter's unsupported outcome. -/
theorem step_length_arguments_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (values : List Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.builtin .len) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.builtin .len) values, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.builtin .len) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases values with
  | nil => apply Preserves.unchanged layout <;> trivial
  | cons value rest =>
    cases rest with
    | nil =>
      exact step_length_preserves module logical physical rename logicalAnchors physicalAnchors
        value stack globals layout (inside.1.2 value (by simp)) inside.2 globalsInside
    | cons next rest => apply Preserves.unchanged layout <;> trivial

end FormalSW.PyAst.HeapCalls.Relocation
