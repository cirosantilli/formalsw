import lang.py.FormalSW.MachineBuiltinDispatch
import lang.py.FormalSW.MachineNamedCallInvariant
import lang.py.FormalSW.MachineCollectorInvariant
import lang.py.FormalSW.MachineGeneratorConsumers
import lang.py.FormalSW.MachineMembershipInvariant
import lang.py.FormalSW.MachineItemInvariant
import lang.py.FormalSW.MachineSliceInvariant
import lang.py.FormalSW.MachineListMethods
import lang.py.FormalSW.MachineSequenceMethods
import lang.py.FormalSW.MachineStringMethods
import lang.py.FormalSW.MachineExceptionInvariant
import lang.py.FormalSW.MachineSingletonDictionary

/-! Complete operation dispatch retains live values, saved callers and source definitions. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem step_operation_preserves (module : Module)
    (source : ∀ statement ∈ module.body, StmtWithin 0 statement)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (operation : Operation) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation operation values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation operation values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation operation values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases operation with
  | call name =>
    exact step_named_call_preserves module name source logical physical rename logicalAnchors physicalAnchors
      values stack globals layout inside globalsInside
  | method receiver args body =>
    exact step_method_preserves module logical physical rename logicalAnchors physicalAnchors
      receiver args body values stack globals layout inside globalsInside
  | notCallable =>
    exact step_notCallable_preserves module logical physical rename logicalAnchors physicalAnchors
      values stack globals layout inside globalsInside
  | setField name value =>
    rcases values with _ | ⟨receiver, _ | ⟨extra, rest⟩⟩
    case cons.nil =>
      exact step_setField_preserves module logical physical rename logicalAnchors physicalAnchors
        receiver value name stack globals layout inside globalsInside
    all_goals exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  | raiseException typeName =>
    exact step_raiseException_preserves module logical physical rename logicalAnchors physicalAnchors
      typeName values stack globals layout inside.2 globalsInside
  | subscript =>
    rcases values with _ | ⟨receiver, _ | ⟨index, _ | ⟨extra, rest⟩⟩⟩
    case cons.cons.nil =>
      exact step_subscript_preserves module logical physical rename logicalAnchors physicalAnchors
        receiver index stack globals layout inside globalsInside
    all_goals exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  | setItem value =>
    rcases values with _ | ⟨receiver, _ | ⟨index, _ | ⟨extra, rest⟩⟩⟩
    case cons.cons.nil =>
      exact step_setItem_preserves module logical physical rename logicalAnchors physicalAnchors
        receiver index value stack globals layout inside globalsInside
    all_goals exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  | membership negated =>
    rcases values with _ | ⟨needle, _ | ⟨container, _ | ⟨extra, rest⟩⟩⟩
    case cons.cons.nil =>
      exact step_membership_preserves module logical physical rename logicalAnchors physicalAnchors
        needle container negated stack globals layout inside globalsInside
    all_goals exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  | builtin name =>
    exact step_builtin_preserves module logical physical rename logicalAnchors physicalAnchors
      name values stack globals layout inside globalsInside
  | isDigit receiver =>
    exact step_isDigit_preserves module logical physical rename logicalAnchors physicalAnchors
      receiver values stack globals layout inside globalsInside
  | list =>
    exact step_sequenceConstruction_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout .listDisplay inside globalsInside
  | tuple =>
    exact step_sequenceConstruction_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout .tupleDisplay inside globalsInside
  | reversedList =>
    exact step_sequenceConstruction_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout .reverse inside globalsInside
  | slice =>
    exact step_slice_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout .read inside globalsInside
  | setSlice value =>
    exact step_slice_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.write value) inside globalsInside
  | append address =>
    exact step_sequenceMutation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.append address) inside globalsInside
  | pop address =>
    exact step_sequenceMutation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.pop address) inside globalsInside
  | count address =>
    exact step_listMethod_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.count address) inside globalsInside
  | sort address =>
    exact step_listMethod_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.sort address) inside globalsInside
  | sortReverse address =>
    exact step_listMethod_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.sortReverse address) inside globalsInside
  | replace text =>
    exact step_stringMethod_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.replace text) inside globalsInside
  | zfill text =>
    exact step_stringMethod_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.zfill text) inside globalsInside
  | upper text =>
    exact step_stringMethod_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.upper text) inside globalsInside
  | strip text =>
    exact step_stringMethod_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.strip text) inside globalsInside
  | splitWhitespace text =>
    exact step_stringMethod_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.split text) inside globalsInside
  | join text =>
    exact step_stringMethod_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.join text) inside globalsInside
  | add address =>
    exact step_setConstruction_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.add address) inside globalsInside
  | dictionarySingleton =>
    rcases values with _ | ⟨key, _ | ⟨value, _ | ⟨extra, rest⟩⟩⟩
    case cons.cons.nil =>
      exact step_dictionarySingleton_preserves module logical physical rename logicalAnchors physicalAnchors
        key value stack globals layout inside globalsInside
    all_goals
      apply Preserves.unchanged layout
      · rfl
      · simpa [step, primitive, Mutable.error, result, run, done, protectGenerator,
          StepWithin, CompletionWithin, Calls.generatorException] using globalsInside
      · simp [step, primitive, result, run, Mutable.error, done, protectGenerator,
          relocateState, relocateWork, relocateRuntimeOperation, relocateOperation,
          relocateStep, relocateCompletion, Calls.generatorException, Except.map]
  | dictionaryGet address =>
    exact step_dictionaryOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.get address) inside globalsInside
  | dictionarySetDefault address =>
    exact step_dictionaryOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.setdefault address) inside globalsInside
  | dictionaryClear address =>
    exact step_dictionaryOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.clear address) inside globalsInside
  | comprehensionStore address =>
    exact step_dictionaryOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.store address) inside globalsInside
  | comprehension element generators env =>
    exact step_collectorOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.listSimple element generators env) inside globalsInside
  | comprehensionTargets element generators env =>
    exact step_collectorOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.list element generators env) inside globalsInside
  | setComprehension element generators env =>
    exact step_collectorOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.set element generators env) inside globalsInside
  | dictionaryComprehension key value generators env =>
    exact step_collectorOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.dictionary key value generators env) inside globalsInside
  | generatorCollect action element generators env =>
    exact step_collectorOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.generator action element generators env) inside globalsInside
  | sumGenerator element generators env start =>
    exact step_generatorConsumerOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.sumSimple element generators env start) inside globalsInside
  | sumGeneratorTargets element generators env start =>
    exact step_generatorConsumerOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.sum element generators env start) inside globalsInside
  | truthGenerator universal element generators env =>
    exact step_generatorConsumerOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.truth universal element generators env) inside globalsInside
  | extremumGenerator maximum fallback element generators env =>
    exact step_generatorConsumerOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.extremum maximum fallback element generators env) inside globalsInside
  | nextGenerator fallback element generators env =>
    exact step_generatorConsumerOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.next fallback element generators env) inside globalsInside
  | sumSequence =>
    exact step_sequenceOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout .sum inside globalsInside
  | permutationStart target body otherwise following env =>
    exact step_sequenceOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.permutation target body otherwise following env) inside globalsInside
  | combinationStart target body otherwise following env =>
    exact step_sequenceOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.combination target body otherwise following env) inside globalsInside
  | zipStart target body otherwise following env =>
    exact step_sequenceOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.zip target body otherwise following env) inside globalsInside

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_operation_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (operation : Operation) (values : List Mutable.Value) (stack : List HeapCalls.Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
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
    (HeapCalls.Relocation.step_operation_preserves module source logical physical rename logicalAnchors physicalAnchors
      operation values stack globals layout ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation

