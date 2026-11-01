import lang.py.FormalSW.MachineGeneratorEntry
import lang.py.FormalSW.MachineControlInvariant
import lang.py.FormalSW.MachineConstructionInvariant
import lang.py.FormalSW.MachineComparisonInvariant
import lang.py.FormalSW.MachineMembershipInvariant
import lang.py.FormalSW.MachineItemInvariant

/-! Expression entry preserves captured roots before its operands execute. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false


variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_generator_expression_preserves (consumer element : Expr)
    (generators : List (Expr × Expr × List Expr)) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.consumeGenerator consumer element generators) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.consumeGenerator consumer element generators) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.expr (.consumeGenerator consumer element generators) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have envInside : EnvWithin logical.length env := inside.1
  have stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame := inside.2
  simp only [relocateState, relocateWork, step_generator_entry]
  cases generatorEntry consumer element generators with
  | unsupported => exact Preserves.unchanged layout trivial trivial rfl
  | expanded name expressions =>
    exact expanded_arguments_entry_preserves logical physical rename physicalAnchors (.call name) env [] expressions stack
      layout (by trivial) envInside (by simp) stackInside
  | next => apply next_generator_arguments_preserves <;> assumption
  | extremum => apply extremum_generator_arguments_preserves <;> assumption
  | truth => apply truth_generator_arguments_preserves <;> assumption
  | collect => apply generator_arguments_preserves <;> assumption
  | tuple => exact Preserves.unchanged layout rfl ⟨envInside, stackInside⟩ rfl
  | resume =>
    apply Preserves.unchanged layout
    · rfl
    · refine ⟨envInside, ?_⟩
      intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · simpa only [FrameWithin] using stackInside
      · exact withoutGenerator_within logical.length stack stackInside frame member
    · simp only [generatorEntryStep, relocateStep, relocateState, relocateWork, List.map_cons,
        relocateFrame, withoutGenerator_relocates]
  | exhausted =>
    apply Preserves.unchanged layout
    · rfl
    · exact ⟨⟨by trivial, by simp⟩, withoutGenerator_within logical.length stack stackInside⟩
    · simp only [generatorEntryStep, relocateStep, relocateState, relocateWork, List.map_nil,
        relocateRuntimeOperation, relocateOperation, withoutGenerator_relocates]
  | join receiver =>
    apply Preserves.unchanged layout
    · rfl
    · refine ⟨envInside, ?_⟩
      intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · simpa only [FrameWithin] using envInside
      · exact stackInside frame member
    · simp only [generatorEntryStep, relocateStep, relocateState, relocateWork, List.map_cons, relocateFrame]

/-- Every modeled expression entry preserves roots, including unsupported forms and failed lookups. -/
theorem step_expression_preserves (expression : Expr) (env : Env) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr expression env, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr expression env, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.expr expression env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases expression with
  | constant => apply step_constant_preserves <;> assumption
  | name => apply step_lookup_preserves <;> assumption
  | «attribute» => apply step_attribute_expression_preserves <;> assumption
  | list => apply step_list_expression_preserves <;> assumption
  | tuple => apply step_tuple_expression_preserves <;> assumption
  | dict => apply step_dictionary_expression_preserves <;> assumption
  | binOp => apply step_binary_expression_preserves <;> assumption
  | unaryOp => apply step_unary_expression_preserves <;> assumption
  | compare => apply step_compare_expression_preserves <;> assumption
  | boolOp => apply step_boolean_expression_preserves <;> assumption
  | ifExp => apply step_conditional_expression_preserves <;> assumption
  | membership => apply step_membership_expression_preserves <;> assumption
  | call => apply step_call_expression_preserves <;> assumption
  | builtinCall => apply step_builtin_expression_preserves <;> assumption
  | subscript => apply step_subscript_expression_preserves <;> assumption
  | consumeGenerator => apply step_generator_expression_preserves <;> assumption
  | ellipsis | extremumRange | zipIterable | permutationsIterable | combinationsIterable | dictionaryValuesIterable | slice =>
    apply Preserves.unchanged layout <;>
      simp only [step, relocateState, relocateWork, relocateStep, protectGenerator, StepHeap, StepWithin]
  | sumRange => exact Preserves.unchanged layout rfl inside rfl
  | sortedSequence | extremumSequence =>
    apply Preserves.unchanged layout
    · rfl
    · refine ⟨inside.1, ?_⟩
      intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · simpa only [FrameWithin] using inside.1
      · exact inside.2 frame member
    · simp only [step, relocateState, relocateWork, relocateStep, relocateFrame, List.map_cons, protectGenerator_next]
  | sumSequence iterable start =>
    exact arguments_entry_preserves logical physical rename physicalAnchors .sumSequence env [] [iterable, start] stack
      layout (by trivial) inside.1 (by simp) inside.2
  | reversedList iterable =>
    exact arguments_entry_preserves logical physical rename physicalAnchors .reversedList env [] [iterable] stack
      layout (by trivial) inside.1 (by simp) inside.2
  | sumGenerator element generators start =>
    cases generators with
    | nil =>
      apply Preserves.unchanged layout <;>
        simp only [step, relocateState, relocateWork, relocateStep, protectGenerator, StepHeap, StepWithin]
    | cons generator rest =>
      rcases generator with ⟨name, iterable, filters⟩
      simp only [step, relocateState, relocateWork, protectGenerator_next]
      apply arguments_entry_preserves
      · exact layout
      · exact inside.1
      · exact inside.1
      · simp
      · exact inside.2
  | listComp element generators =>
    cases generators with
    | nil =>
      apply Preserves.unchanged layout <;>
        simp only [step, relocateState, relocateWork, relocateStep, protectGenerator, StepHeap, StepWithin]
    | cons generator rest =>
      rcases generator with ⟨name, iterable, filters⟩
      simp only [step, relocateState, relocateWork, protectGenerator_next]
      rw [SetCalls.Relocation.comprehensionEnv_relocates]
      apply arguments_entry_preserves
      · exact layout
      · exact SetCalls.Relocation.comprehensionEnv_within logical.length env _ inside.1
      · exact inside.1
      · simp
      · exact inside.2
  | listCompTargets element generators =>
    cases generators with
    | nil =>
      apply Preserves.unchanged layout <;>
        simp only [step, relocateState, relocateWork, relocateStep, protectGenerator, StepHeap, StepWithin]
    | cons generator rest =>
      rcases generator with ⟨target, iterable, filters⟩
      simp only [step, relocateState, relocateWork, protectGenerator_next]
      rw [SetCalls.Relocation.comprehensionTargetsEnv_relocates]
      apply arguments_entry_preserves
      · exact layout
      · exact SetCalls.Relocation.comprehensionTargetsEnv_within logical.length env _ inside.1
      · exact inside.1
      · simp
      · exact inside.2
  | setComp element generators =>
    cases generators with
    | nil =>
      apply Preserves.unchanged layout <;>
        simp only [step, relocateState, relocateWork, relocateStep, protectGenerator, StepHeap, StepWithin]
    | cons generator rest =>
      rcases generator with ⟨target, iterable, filters⟩
      simp only [step, relocateState, relocateWork, protectGenerator_next]
      rw [SetCalls.Relocation.comprehensionTargetsEnv_relocates]
      apply arguments_entry_preserves
      · exact layout
      · exact SetCalls.Relocation.comprehensionTargetsEnv_within logical.length env _ inside.1
      · exact inside.1
      · simp
      · exact inside.2
  | dictComp key value generators =>
    cases generators with
    | nil =>
      apply Preserves.unchanged layout <;>
        simp only [step, relocateState, relocateWork, relocateStep, protectGenerator, StepHeap, StepWithin]
    | cons generator rest =>
      rcases generator with ⟨target, iterable, filters⟩
      simp only [step, relocateState, relocateWork, protectGenerator_next]
      rw [SetCalls.Relocation.comprehensionTargetsEnv_relocates]
      apply arguments_entry_preserves
      · exact layout
      · exact SetCalls.Relocation.comprehensionTargetsEnv_within logical.length env _ inside.1
      · exact inside.1
      · simp
      · exact inside.2
  | sumGeneratorTargets element generators start =>
    cases generators with
    | nil =>
      apply Preserves.unchanged layout <;>
        simp only [step, relocateState, relocateWork, relocateStep, protectGenerator, StepHeap, StepWithin]
    | cons generator rest =>
      rcases generator with ⟨target, iterable, filters⟩
      simp only [step, relocateState, relocateWork, protectGenerator_next]
      apply arguments_entry_preserves
      · exact layout
      · exact inside.1
      · exact inside.1
      · simp
      · exact inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

/-- Expression entry needs no assumed core-preservation premise, including iterator interception and set fallback. -/
theorem step_expression_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (expression : Expr) (env : HeapCalls.Env) (stack : List HeapCalls.Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin logical.length (.running ⟨⟨.expr expression env, stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running ⟨⟨.expr expression env, stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running ⟨⟨.expr expression env, stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running ⟨⟨.expr expression env, stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals
    source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_expression_preserves module logical physical rename logicalAnchors physicalAnchors
      expression env stack globals layout ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
