import lang.py.FormalSW.MachineCursorInvariant

/-! Every statement-block transition preserves the execution invariant. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_block_preserves (body : List Stmt) (env : Env) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block body env, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block body env, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.block body env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases body with
  | nil => exact step_empty_block_preserves module logical physical rename logicalAnchors physicalAnchors env stack globals layout inside
  | cons statement following =>
    cases statement with
    | «return» => apply step_return_preserves <;> assumption
    | assign => apply step_assignment_preserves <;> assumption
    | annAssign => apply step_annotation_preserves <;> assumption
    | augAssign => apply step_augmented_assignment_preserves <;> assumption
    | forIn => apply step_for_preserves <;> assumption
    | dictionaryItemsStepLoop => apply step_dictionary_items_loop_preserves <;> assumption
    | zipStepLoop => apply step_zip_loop_preserves <;> assumption
    | permutationStepLoop => apply step_positional_loop_preserves <;> assumption
    | rangeStepLoop => apply step_range_loop_preserves <;> assumption
    | sequenceStepLoop => apply step_sequence_loop_preserves <;> assumption
    | reverseSequenceStepLoop => apply step_reverse_loop_preserves <;> assumption
    | enumerateStepLoop => apply step_enumerate_loop_preserves <;> assumption
    | unpackStepLoop => apply step_unpack_loop_preserves <;> assumption
    | ifThen => apply step_if_statement_preserves <;> assumption
    | whileDo => apply step_while_preserves <;> assumption
    | breakLoop => apply step_break_preserves <;> assumption
    | continueLoop => apply step_continue_preserves <;> assumption
    | loopResume => apply step_loopResume_preserves <;> assumption
    | «assert» => apply step_assert_preserves <;> assumption
    | expr => apply step_expression_statement_preserves <;> assumption
    | classDef | dataclassFields | functionDef | globalDecl | rangeLoop | setStepLoop | unsupported | importFrom | importModules =>
      apply Preserves.unchanged layout <;> simp only [step, relocateState, relocateWork, List.map_cons, relocateStmt, protectGenerator, relocateStep, StepHeap, StepWithin]
    | forDictionaryItems =>
      apply Preserves.unchanged layout
      · rfl
      · apply StateWithin.for_dictionary_items <;> assumption
      · exact step_for_dictionary_items_relocates ..
    | forReversed =>
      apply Preserves.unchanged layout
      · rfl
      · apply StateWithin.for_reversed <;> assumption
      · exact step_for_reversed_relocates ..
    | forZip =>
      apply Preserves.unchanged layout
      · exact argumentsState_heap ..
      · apply StateWithin.for_zip <;> assumption
      · exact step_for_zip_relocates ..
    | comprehensionAppend address expression =>
      apply Preserves.unchanged layout
      · exact argumentsState_heap ..
      · apply argumentsState_within logical (.append address) env [] [expression] (.discard following env :: stack)
        · simpa only [StmtWithin, OperationWithin] using inside.1.2 _ (List.mem_cons_self ..)
        · exact inside.1.1
        · simp
        · intro frame member
          rcases List.mem_cons.mp member with rfl | member
          · simp only [FrameWithin]
            exact ⟨inside.1.1, fun statement member => inside.1.2 statement (List.mem_cons_of_mem _ member)⟩
          · exact inside.2 frame member
      · simpa only [step, relocateState, relocateWork, List.map_cons, relocateStmt, protectGenerator_next,
          relocateStep, relocateFrame, relocateRuntimeOperation, relocateOperation] using
          congrArg Step.next (argumentsState_relocates rename logical physical
            (.append address) env [] [expression] (.discard following env :: stack))
    | comprehensionAdd address expression =>
      apply Preserves.unchanged layout
      · exact argumentsState_heap ..
      · apply argumentsState_within logical (.add address) env [] [expression] (.discard following env :: stack)
        · simpa only [StmtWithin, OperationWithin] using inside.1.2 _ (List.mem_cons_self ..)
        · exact inside.1.1
        · simp
        · intro frame member
          rcases List.mem_cons.mp member with rfl | member
          · simp only [FrameWithin]
            exact ⟨inside.1.1, fun statement member => inside.1.2 statement (List.mem_cons_of_mem _ member)⟩
          · exact inside.2 frame member
      · simpa only [step, relocateState, relocateWork, List.map_cons, relocateStmt, protectGenerator_next,
          relocateStep, relocateFrame, relocateRuntimeOperation, relocateOperation] using
          congrArg Step.next (argumentsState_relocates rename logical physical
            (.add address) env [] [expression] (.discard following env :: stack))
    | comprehensionStore address key value =>
      apply Preserves.unchanged layout
      · exact argumentsState_heap ..
      · apply argumentsState_within logical (.comprehensionStore address) env [] [key, value] (.discard following env :: stack)
        · simpa only [StmtWithin, OperationWithin] using inside.1.2 _ (List.mem_cons_self ..)
        · exact inside.1.1
        · simp
        · intro frame member
          rcases List.mem_cons.mp member with rfl | member
          · simp only [FrameWithin]
            exact ⟨inside.1.1, fun statement member => inside.1.2 statement (List.mem_cons_of_mem _ member)⟩
          · exact inside.2 frame member
      · simpa only [step, relocateState, relocateWork, List.map_cons, relocateStmt, protectGenerator_next,
          relocateStep, relocateFrame, relocateRuntimeOperation, relocateOperation] using
          congrArg Step.next (argumentsState_relocates rename logical physical
            (.comprehensionStore address) env [] [key, value] (.discard following env :: stack))
    | raise exception =>
      cases exception with
      | none => apply Preserves.unchanged layout <;> simp only [step, relocateState, relocateWork, List.map_cons, relocateStmt, protectGenerator, relocateStep, StepHeap, StepWithin]
      | some expression =>
        cases expression with
        | name => apply step_raise_name_preserves <;> assumption
        | call callee arguments =>
          cases callee with
          | name => apply step_raise_call_preserves <;> assumption
          | _ => apply Preserves.unchanged layout <;> simp only [step, relocateState, relocateWork, List.map_cons, relocateStmt, protectGenerator, relocateStep, StepHeap, StepWithin]
        | _ => apply Preserves.unchanged layout <;> simp only [step, relocateState, relocateWork, List.map_cons, relocateStmt, protectGenerator, relocateStep, StepHeap, StepWithin]

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

/-- Statement blocks need no assumed core-preservation premise, including intercepted iterators and set fallback. -/
theorem step_block_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (body : List Stmt) (env : HeapCalls.Env) (stack : List HeapCalls.Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin logical.length (.running ⟨⟨.block body env, stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running ⟨⟨.block body env, stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running ⟨⟨.block body env, stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running ⟨⟨.block body env, stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals
    source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_block_preserves module logical physical rename logicalAnchors physicalAnchors
      body env stack globals layout ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
