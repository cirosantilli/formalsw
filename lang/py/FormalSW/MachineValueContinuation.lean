import lang.py.FormalSW.MachineValueResults
import lang.py.FormalSW.MachineExtremumSelection
import lang.py.FormalSW.MachineExpressionEntry
import lang.py.FormalSW.MachineStarredInvariant
import lang.py.FormalSW.MachineLoopAcquisition
import lang.py.FormalSW.MachineGeneratorContinuation
import lang.py.FormalSW.MachineBinaryInvariant
import lang.py.FormalSW.MachineExceptionInvariant

/-! Value dispatch isolates the remaining recursive-comparison obligation. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- Only comparison-bearing frames restrict the domain; other continuations cover every modeled outcome. -/
def ValueComparisonDomain (heap : Mutable.Heap) (value : Value) : List Frame → Prop
  | .compareRight op left :: _ | .chainRight op left _ _ :: _ => NonrecursiveComparison heap op left value
  | .extremumKey cursor _ _ best :: _ => ExtremumComparison heap cursor value best
  | _ => True

theorem step_value_continuation_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (source : ∀ statement ∈ module.body, StmtWithin 0 statement)
    (inside : StateWithin ⟨.value value, stack, logical⟩) (globalsInside : GlobalsWithin logical.length globals)
    (comparison : ValueComparisonDomain logical value stack) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value value, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases stack with
  | nil => exact step_value_preserves module logical physical rename logicalAnchors physicalAnchors value globals layout inside.1 globalsInside
  | cons frame stack =>
    cases frame with
    | sortedSource => apply step_sortedSource_preserves <;> assumption
    | sortedReverse => apply step_sortedReverse_preserves <;> assumption
    | sortedKey => apply step_sortedKey_preserves <;> assumption
    | extremumSource => apply step_extremumSource_preserves <;> assumption
    | extremumKey => apply step_extremumKey_preserves <;> assumption
    | dictionaryItemsReceiver => apply step_dictionary_items_start_preserves <;> assumption
    | dictionaryValuesReceiver => apply step_dictionary_values_start_preserves <;> assumption
    | dictionaryKey => apply step_dictionaryKey_preserves <;> assumption
    | dictionaryValue => apply step_dictionaryValue_preserves <;> assumption
    | sumStart => apply step_sumStart_preserves <;> assumption
    | extremumStart => apply step_extremumStart_preserves <;> assumption
    | extremumResume => apply step_extremumResume_preserves <;> assumption
    | generatorEnd => apply step_generatorEnd_preserves <;> assumption
    | generatorConsumer => apply step_generatorConsumer_preserves <;> assumption
    | generatorReceiver => apply step_generatorReceiver_preserves <;> assumption
    | initialized => apply step_initialized_preserves <;> assumption
    | «attribute» => apply step_attribute_preserves <;> assumption
    | methodReceiver => apply step_methodReceiver_preserves <;> assumption
    | assignAttribute => apply step_assignAttribute_preserves <;> assumption
    | augmentAttribute => apply step_augmentAttribute_preserves <;> assumption
    | writeAttribute => apply step_writeAttribute_preserves <;> assumption
    | comprehensionResult => apply step_comprehensionResult_preserves <;> assumption
    | binaryLeft => apply step_binaryLeft_preserves <;> assumption
    | binaryRight => apply step_binary_preserves <;> assumption
    | compareLeft => apply step_compareLeft_preserves <;> assumption
    | compareRight => apply step_compare_nonrecursive_preserves <;> assumption
    | chainLeft => apply step_chainLeft_preserves <;> assumption
    | chainRight => apply step_chainCompare_nonrecursive_preserves <;> assumption
    | chainResult => apply step_chainResult_preserves <;> assumption
    | unary => apply step_unary_preserves <;> assumption
    | boolean => apply step_boolean_preserves <;> assumption
    | conditional => apply step_conditional_preserves <;> assumption
    | arguments => apply step_arguments_preserves <;> assumption
    | starredArguments => apply step_starredArguments_preserves <;> assumption
    | appendReceiver => apply step_appendReceiver_preserves <;> assumption
    | addReceiver => apply step_addReceiver_preserves <;> assumption
    | assign => apply step_assign_preserves <;> assumption
    | unpack => apply step_unpack_preserves <;> assumption
    | branch => apply step_branch_preserves <;> assumption
    | discard => apply step_discard_preserves <;> assumption
    | assertion => apply step_assertion_preserves <;> assumption
    | assertionMessage => apply step_assertionMessage_preserves <;> assumption
    | reverseSequence => apply step_reverse_start_preserves <;> assumption
    | sequence => apply step_sequence_start_preserves <;> assumption
    | unpackSequence => apply step_unpack_start_preserves <;> assumption
    | enumerateSource => apply step_enumerate_source_preserves <;> assumption
    | enumerateStart => apply step_enumerate_start_preserves <;> assumption
    | augmentItemReceiver => apply step_augmentItemReceiver_preserves <;> assumption
    | augmentItemIndex => apply step_augmentItemIndex_preserves <;> assumption
    | writeItem => apply step_writeItem_preserves <;> assumption
    | assignItem => apply step_assignItem_preserves <;> assumption
    | assignSlice => apply step_assignSlice_preserves <;> assumption
    | rangeArguments => apply step_range_arguments_preserves <;> assumption
    | nextStart => apply step_nextStart_preserves <;> assumption

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_value_continuation_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (value : Mutable.Value) (stack : List HeapCalls.Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin logical.length (.running ⟨⟨.value value, stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) (comparison : ValueComparisonDomain logical value stack) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running ⟨⟨.value value, stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running ⟨⟨.value value, stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running ⟨⟨.value value, stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_value_continuation_preserves module logical physical rename logicalAnchors physicalAnchors
      value stack globals layout source ⟨inside.1, inside.2.1⟩ globalsInside comparison)

end FormalSW.PyAst.IteratorCalls.Relocation
