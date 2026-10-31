import lang.py.FormalSW.BytesElementRelocation
import lang.py.FormalSW.MachineSliceInvariant

/-! Buffer constructors retain prior effects and validate contents before fresh allocation. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

def bytesEncode (action : Mutable.Eval (List UInt8)) : Mutable.Eval Value :=
  (fun bytes => .scalar (.bytes bytes)) <$> action

theorem result_bytesEncode_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (action otherAction : Mutable.Eval (List UInt8)) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals)
    (readonly : ∀ outcome after, action logical = some (outcome, after) → after = logical)
    (paired : otherAction physical = (action logical).map (fun pair => (pair.1, physical))) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (bytesEncode action) stack globals)
      (result physicalAnchors physical (bytesEncode otherAction) (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have normalized (action : Mutable.Eval (List UInt8)) : bytesEncode action =
      (do let bytes ← action; pure (.scalar (.bytes bytes))) := by
    funext heap
    cases executed : action heap with
    | none => simp [bytesEncode, Mutable.eval_map, Mutable.eval_bind, executed]
    | some pair =>
      rcases pair with ⟨outcome, after⟩
      cases outcome <;> simp [bytesEncode, Mutable.eval_map, Mutable.eval_bind, executed, Except.map]
  rw [normalized, normalized, result_bind, result_bind]
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ id _ _ globals layout globalsInside readonly
    (by simpa only [Except.map_id] using paired)
  intro bytes _
  exact result_pure_preserves logical physical rename logicalAnchors physicalAnchors (.scalar (.bytes bytes)) stack globals layout (by trivial) stackInside

theorem result_byteValuesEncode_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (source : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (sourceInside : source.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (bytesEncode (Mutable.byteValues source)) stack globals)
      (result physicalAnchors physical (bytesEncode (Mutable.byteValues (relocateValue rename source)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  exact result_bytesEncode_preserves logical physical rename logicalAnchors physicalAnchors _ _ stack globals layout stackInside globalsInside
    (fun outcome after executed => byteValues_heap logical after source outcome executed)
    (layout.runtime.byteValues source sourceInside)

theorem bytes_ref (heap : Mutable.Heap) (address : Nat) (object : Mutable.Object)
    (found : heap[address]? = some object) :
    Mutable.bytes [.ref address] heap = (match object with
      | .list items | .tuple items => bytesEncode (items.mapM Mutable.bytesElement)
      | .bytearray _ => bytesEncode (Mutable.byteValues (.ref address))
      | _ => Mutable.unsupported) heap := by
  cases object <;> simp [Mutable.bytes, found, bytesEncode] <;> rfl

theorem bytes_many (first second : Value) (rest : List Value) :
    Mutable.bytes (first :: second :: rest) =
      if 3 < (first :: second :: rest).length then Mutable.error "TypeError" else Mutable.unsupported := by
  cases first with
  | scalar scalar => cases scalar <;> rfl
  | ref address => rfl

theorem result_bytes_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.bytes values) stack globals)
      (result physicalAnchors physical (Mutable.bytes (values.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  rcases values with _ | ⟨value, _ | ⟨second, rest⟩⟩
  case nil =>
    exact result_pure_preserves logical physical rename logicalAnchors physicalAnchors (.scalar (.bytes [])) stack globals layout (by trivial) stackInside
  case cons.nil =>
    have valueInside := valuesInside value (by simp)
    cases value with
    | scalar scalar =>
      cases scalar with
      | int size =>
        by_cases outside : size < -2147483648 ∨ 2147483648 ≤ size
        · apply Preserves.unchanged layout <;>
            simp [result, run, Mutable.bytes, relocateValue, outside, Mutable.unsupported, StepHeap, StepWithin, relocateStep]
        · by_cases negative : size < 0
          · simpa only [Mutable.bytes, List.map_cons, List.map_nil, relocateValue, outside, negative, if_false, if_true] using
              result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
                (some (.error ⟨"ValueError", []⟩)) stack globals layout stackInside globalsInside
          · simpa only [Mutable.bytes, List.map_cons, List.map_nil, relocateValue, outside, negative, if_false] using
              result_pure_preserves logical physical rename logicalAnchors physicalAnchors (.scalar (.bytes (List.replicate size.toNat 0)))
                stack globals layout (by trivial) stackInside
      | bool flag =>
        exact result_pure_preserves logical physical rename logicalAnchors physicalAnchors (.scalar (.bytes (if flag then [0] else [])))
          stack globals layout (by trivial) stackInside
      | string text | bytes data | none =>
        exact result_byteValuesEncode_preserves logical physical rename logicalAnchors physicalAnchors _ stack globals layout valueInside stackInside globalsInside
    | ref address =>
      have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem valueInside
      have moved := layout.runtime.lookup address _ found
      cases object : logical[address] <;> simp only [object, relocateObject] at moved
      all_goals
        simp only [result, run, List.map_cons, List.map_nil, relocateValue,
          bytes_ref logical address _ (found.trans (congrArg some object)), bytes_ref physical (rename address) _ moved]
      case list items | tuple items =>
        have bounded := layout.closed _ (List.mem_of_getElem? (found.trans (congrArg some object)))
        exact result_bytesEncode_preserves logical physical rename logicalAnchors physicalAnchors _ _ stack globals layout stackInside globalsInside
          (fun outcome after executed => bytesElements_heap logical after items bounded outcome executed)
          (layout.runtime.bytesElements items bounded)
      case bytearray bytes =>
        exact result_byteValuesEncode_preserves logical physical rename logicalAnchors physicalAnchors (.ref address) stack globals layout valueInside stackInside globalsInside
      all_goals exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  case cons.cons =>
    simp only [List.map_cons, bytes_many, List.length_cons, List.length_map]
    by_cases excessive : 3 < rest.length + 1 + 1
    · simp only [excessive, if_true]
      exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout stackInside globalsInside
    · simp only [excessive, if_false]
      exact Preserves.unchanged layout (by trivial) (by trivial) rfl

theorem result_bytearrayCopy_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (source : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (sourceInside : source.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (do let bytes ← Mutable.byteValues source; Mutable.allocateBuffer bytes) stack globals)
      (result physicalAnchors physical (do let bytes ← Mutable.byteValues (relocateValue rename source); Mutable.allocateBuffer bytes)
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  rw [result_bind, result_bind]
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ id _ _ globals layout globalsInside
    (fun outcome after executed => byteValues_heap logical after source outcome executed)
    (by simpa only [Except.map_id] using layout.runtime.byteValues source sourceInside)
  intro bytes _
  exact result_allocateBuffer_preserves logical physical rename logicalAnchors physicalAnchors bytes stack globals layout stackInside globalsInside

theorem result_bytearray_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.bytearray values) stack globals)
      (result physicalAnchors physical (Mutable.bytearray (values.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  rcases values with _ | ⟨value, _ | ⟨second, rest⟩⟩
  case nil => exact result_allocateBuffer_preserves logical physical rename logicalAnchors physicalAnchors [] stack globals layout stackInside globalsInside
  case cons.nil =>
    have valueInside := valuesInside value (by simp)
    cases value with
    | scalar scalar =>
      cases scalar with
      | int size =>
        by_cases negative : size < 0
        · simpa only [Mutable.bytearray, List.map_cons, List.map_nil, relocateValue, negative, if_true] using
            result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
              (some (.error ⟨"ValueError", []⟩)) stack globals layout stackInside globalsInside
        · simpa only [Mutable.bytearray, List.map_cons, List.map_nil, relocateValue, negative, if_false] using
            result_allocateBuffer_preserves logical physical rename logicalAnchors physicalAnchors (List.replicate size.toNat 0)
              stack globals layout stackInside globalsInside
      | bool flag =>
        exact result_allocateBuffer_preserves logical physical rename logicalAnchors physicalAnchors (if flag then [0] else [])
          stack globals layout stackInside globalsInside
      | string text | bytes data | none =>
        exact result_bytearrayCopy_preserves logical physical rename logicalAnchors physicalAnchors _ stack globals layout valueInside stackInside globalsInside
    | ref address =>
      exact result_bytearrayCopy_preserves logical physical rename logicalAnchors physicalAnchors (.ref address) stack globals layout valueInside stackInside globalsInside
  case cons.cons =>
    cases value with
    | scalar scalar =>
      cases scalar <;>
        exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
          (some (.error ⟨"TypeError", []⟩)) stack globals layout stackInside globalsInside
    | ref address =>
      exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout stackInside globalsInside

inductive BufferConstructionOperation : Operation → Prop
  | mutableBuffer : BufferConstructionOperation (.builtin .bytearray)
  | immutableBytes : BufferConstructionOperation (.builtin .bytes)

theorem step_bufferConstruction_preserves (module : Module)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (operation : Operation) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (covered : BufferConstructionOperation operation)
    (inside : StateWithin ⟨.operation operation values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation operation values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation operation values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases covered with
  | mutableBuffer =>
    exact (result_bytearray_preserves logical physical rename logicalAnchors physicalAnchors values stack globals
      layout inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2
  | immutableBytes =>
    exact (result_bytes_preserves logical physical rename logicalAnchors physicalAnchors values stack globals
      layout inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_bufferConstruction_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (operation : Operation) (values : List Mutable.Value) (stack : List Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (covered : BufferConstructionOperation operation)
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
    (HeapCalls.Relocation.step_bufferConstruction_preserves module logical physical rename logicalAnchors physicalAnchors
      operation values stack globals layout covered ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
