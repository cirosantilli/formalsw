import lang.py.FormalSW.NumericBuiltinRelocation
import lang.py.FormalSW.MachineSequenceConstruction

/-! Numeric observations and divmod retain argument effects, errors and fresh tuple results. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_scalarBuiltin_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (operation : Operation) (covered : ScalarBuiltinOperation operation)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (primitive operation values) stack globals)
      (result physicalAnchors physical (primitive (relocateOperation rename operation) (values.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  obtain ⟨outcome, left, right⟩ := scalarBuiltin_pair logical physical rename layout.runtime operation covered values valuesInside
  simpa only [result, run, left, right] using
    result_scalar_preserves logical physical rename logicalAnchors physicalAnchors outcome stack globals layout stackInside globalsInside

def numericFailure (values : List Value) : Mutable.Eval Value := do
  let heap ← get
  if values.any (numericProtocol heap) then Mutable.unsupported else Mutable.error "TypeError"

theorem result_numericFailure_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (numericFailure values) stack globals)
      (result physicalAnchors physical (numericFailure (values.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have normalized (heap : Mutable.Heap) (values : List Value) : numericFailure values heap =
      scalarResult (if values.any (numericProtocol heap) then none else some (.error ⟨"TypeError", []⟩)) heap :=
    numericProtocolFailure_result heap _
  simpa only [result, run, normalized, numericProtocols_relocates logical physical rename layout.runtime values valuesInside] using
    result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
      (if values.any (numericProtocol logical) then none else some (.error ⟨"TypeError", []⟩)) stack globals layout stackInside globalsInside

theorem result_divmod_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.divmod values) stack globals)
      (result physicalAnchors physical (Mutable.divmod (values.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have typeError := result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
    (some (.error ⟨"TypeError", []⟩)) stack globals layout stackInside globalsInside
  rcases values with _ | ⟨left, _ | ⟨right, _ | ⟨extra, rest⟩⟩⟩
  case cons.cons.nil =>
    cases left <;> cases right
    case scalar.scalar left right =>
      simp only [Mutable.divmod, List.map_cons, List.map_nil, relocateValue]
      cases leftNumber : scalarNumber left with
      | none => exact typeError
      | some dividend =>
        cases rightNumber : scalarNumber right with
        | none => exact typeError
        | some divisor =>
          cases computed : Py.Builtin.Int.divMod dividend divisor with
          | ok pair =>
            simp only [computed]
            rcases pair with ⟨quotient, remainder⟩
            exact result_allocateTuple_preserves logical physical rename logicalAnchors physicalAnchors
              [.scalar (.int quotient), .scalar (.int remainder)] stack globals layout
              (by intro value member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> trivial)
              stackInside globalsInside
          | error exception =>
            simp only [computed]
            cases exception <;> first
              | exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
                  (some (.error ⟨"ZeroDivisionError", []⟩)) stack globals layout stackInside globalsInside
              | exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
                  none stack globals layout stackInside globalsInside
    all_goals exact result_numericFailure_preserves logical physical rename logicalAnchors physicalAnchors _ stack globals layout valuesInside stackInside globalsInside
  all_goals try exact typeError
  all_goals cases left
  all_goals try cases right
  all_goals exact typeError

inductive NumericBuiltinOperation : Operation → Prop
  | scalar (operation : Operation) (covered : ScalarBuiltinOperation operation) : NumericBuiltinOperation operation
  | quotientRemainder : NumericBuiltinOperation (.builtin .divmod)

theorem step_numericBuiltin_preserves (module : Module)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (operation : Operation) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (covered : NumericBuiltinOperation operation)
    (inside : StateWithin ⟨.operation operation values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation operation values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation operation values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases covered with
  | scalar operation covered =>
    have raw := result_scalarBuiltin_preserves logical physical rename logicalAnchors physicalAnchors operation covered values stack globals
      layout inside.1.2 inside.2 globalsInside
    cases covered <;> exact raw.protectGenerator stack inside.2
  | quotientRemainder =>
    exact (result_divmod_preserves logical physical rename logicalAnchors physicalAnchors values stack globals
      layout inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_numericBuiltin_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (operation : Operation) (values : List Mutable.Value) (stack : List Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (covered : NumericBuiltinOperation operation)
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
    (HeapCalls.Relocation.step_numericBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      operation values stack globals layout covered ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
