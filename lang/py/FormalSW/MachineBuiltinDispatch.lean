import lang.py.FormalSW.MachineBuiltinInvariant
import lang.py.FormalSW.MachineNumericBuiltins
import lang.py.FormalSW.MachineBufferConstruction
import lang.py.FormalSW.MachineDictionaryConstruction
import lang.py.FormalSW.MachineSetConstruction
import lang.py.FormalSW.MachineExtremumBuiltins
import lang.py.FormalSW.MachineHeapqBuiltins
import lang.py.FormalSW.MachineSequenceOperationInvariant

/-! Every builtin dispatch preserves the execution layout, including cursor entry and failures. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem step_identity_arguments_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.builtin .identity) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.builtin .identity) values, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.builtin .identity) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  rcases values with _ | ⟨left, _ | ⟨right, _ | ⟨extra, rest⟩⟩⟩
  case cons.cons.nil =>
    exact step_identity_preserves module logical physical rename logicalAnchors physicalAnchors left right stack globals
      layout (inside.1.2 left (by simp)) (inside.1.2 right (by simp)) inside.2 globalsInside
  all_goals exact Preserves.unchanged layout (by trivial) (by trivial) rfl

theorem step_builtin_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (name : Builtin) (values : List Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.builtin name) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.builtin name) values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation (.builtin name) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases name with
  | all =>
    exact step_truthSequence_preserves module logical physical rename logicalAnchors physicalAnchors
      true values stack globals layout inside globalsInside
  | any =>
    exact step_truthSequence_preserves module logical physical rename logicalAnchors physicalAnchors
      false values stack globals layout inside globalsInside
  | pow =>
    exact step_numericBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.scalar _ .power) inside globalsInside
  | abs =>
    exact step_numericBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.scalar _ .absolute) inside globalsInside
  | bin =>
    exact step_numericBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.scalar _ .binaryText) inside globalsInside
  | int =>
    exact step_numericBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.scalar _ .integer) inside globalsInside
  | isinstanceInt =>
    exact step_numericBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.scalar _ .integerType) inside globalsInside
  | str =>
    exact step_numericBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.scalar _ .text) inside globalsInside
  | ord =>
    exact step_numericBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.scalar _ .ordinal) inside globalsInside
  | max =>
    exact step_extremumBuiltin_preserves module true logical physical rename logicalAnchors physicalAnchors
      values stack globals layout inside globalsInside
  | min =>
    exact step_extremumBuiltin_preserves module false logical physical rename logicalAnchors physicalAnchors
      values stack globals layout inside globalsInside
  | divmod =>
    exact step_numericBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout .quotientRemainder inside globalsInside
  | intBitLength =>
    exact step_numericBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.scalar _ .bitLength) inside globalsInside
  | intBitCount =>
    exact step_numericBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.scalar _ .bitCount) inside globalsInside
  | identity =>
    exact step_identity_arguments_preserves module logical physical rename logicalAnchors physicalAnchors
      values stack globals layout inside globalsInside
  | len =>
    exact step_length_arguments_preserves module logical physical rename logicalAnchors physicalAnchors
      values stack globals layout inside globalsInside
  | bytearray =>
    exact step_bufferConstruction_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout .mutableBuffer inside globalsInside
  | bytes =>
    exact step_bufferConstruction_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout .immutableBytes inside globalsInside
  | list =>
    exact step_sequenceConstruction_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout .list inside globalsInside
  | tuple =>
    exact step_sequenceConstruction_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout .tuple inside globalsInside
  | set =>
    exact step_setConstruction_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout .constructor inside globalsInside
  | setDisplay =>
    exact step_setConstruction_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout .display inside globalsInside
  | sorted =>
    exact step_sortedBuiltin_preserves module false logical physical rename logicalAnchors physicalAnchors
      values stack globals layout inside globalsInside
  | sortedReverse =>
    exact step_sortedBuiltin_preserves module true logical physical rename logicalAnchors physicalAnchors
      values stack globals layout inside globalsInside
  | heapqHeapify =>
    exact step_heapqBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      _ .heapify values stack globals layout inside globalsInside
  | heapqPush =>
    exact step_heapqBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      _ .push values stack globals layout inside globalsInside
  | heapqPop =>
    exact step_heapqBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      _ .pop values stack globals layout inside globalsInside
  | dict =>
    exact step_dictionaryConstruct_preserves module logical physical rename logicalAnchors physicalAnchors
      values stack globals layout inside globalsInside
  | repr =>
    exact step_numericBuiltin_preserves module logical physical rename logicalAnchors physicalAnchors
      _ values stack globals layout (.scalar _ .representation) inside globalsInside

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_builtin_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (name : Builtin) (values : List Mutable.Value) (stack : List HeapCalls.Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin logical.length (.running ⟨⟨.operation (.builtin name) values, stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running ⟨⟨.operation (.builtin name) values, stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running ⟨⟨.operation (.builtin name) values, stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running ⟨⟨.operation (.builtin name) values, stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_builtin_preserves module logical physical rename logicalAnchors physicalAnchors
      name values stack globals layout ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
