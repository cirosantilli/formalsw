import lang.py.FormalSW.DictionaryConstructionRelocation
import lang.py.FormalSW.MachineDictionaryMethods

/-! Dictionary construction retains allocation order, partial contents and shared aliases. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

def appendObject (object : Mutable.Object) : Mutable.Eval Value := fun heap =>
  some (.ok (.ref heap.length), heap ++ [object])

theorem result_appendObject_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (object : Mutable.Object) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (nonempty : object ≠ .tuple [])
    (objectInside : ObjectWithin logical.length object)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (appendObject object) stack globals)
      (result physicalAnchors physical (appendObject (relocateObject rename object))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  apply result_preserves logical physical _ _ rename (extendMap rename logical.length physical.length)
    logicalAnchors physicalAnchors _ _ stack globals (.ok (.ref logical.length))
    (extendMap_old _ _ _) (by simp) (by simp) (layout.append_existing object nonempty objectInside) stackInside globalsInside
  · intro value same; cases same; simp [Mutable.Value.edge, Graph.Edge.Within]
  · rfl
  · simp only [appendObject, Except.map, relocateValue, extendMap_new]

theorem result_dictionaryFromIterable_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (source : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (sourceInside : source.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (DictionaryConstructor.fromIterable source) stack globals)
      (result physicalAnchors physical (DictionaryConstructor.fromIterable (relocateValue rename source))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  obtain ⟨outcome, after, other, left, right, retained, size, otherSize, bounded⟩ := layout.dictionaryFromIterable source sourceInside
  cases outcome with
  | none =>
    apply Preserves.unchanged layout <;> simp [result, run, left, right, StepHeap, StepWithin, relocateStep]
  | some outcome =>
    exact result_preserves logical physical after other rename (extendMap rename logical.length physical.length)
      logicalAnchors physicalAnchors _ _ stack globals outcome (extendMap_old _ _ _) (by omega) (by omega)
      retained stackInside globalsInside (fun value same => bounded value (congrArg some same)) left right

theorem dictionaryConstruct_ref (heap : Mutable.Heap) (address : Nat) (object : Mutable.Object)
    (found : heap[address]? = some object) :
    DictionaryConstructor.construct [.ref address] heap = (match object with
      | .dict entries => appendObject (.dict entries)
      | .keyDict entries => appendObject (.keyDict entries)
      | _ => DictionaryConstructor.fromIterable (.ref address)) heap := by
  cases object <;> simp [DictionaryConstructor.construct, found, appendObject, Mutable.allocateDict] <;> rfl

theorem result_dictionaryConstruct_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (DictionaryConstructor.construct values) stack globals)
      (result physicalAnchors physical (DictionaryConstructor.construct (values.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
  case nil =>
    exact result_appendObject_preserves logical physical rename logicalAnchors physicalAnchors (.dict []) stack globals
      layout (by simp) (by simp [ObjectWithin, objectValues]) stackInside globalsInside
  case cons.nil =>
    have valueInside := valuesInside value (by simp)
    cases value with
    | scalar scalar =>
      exact result_dictionaryFromIterable_preserves logical physical rename logicalAnchors physicalAnchors (.scalar scalar) stack globals
        layout valueInside stackInside globalsInside
    | ref address =>
      have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem valueInside
      have moved := layout.runtime.lookup address _ found
      have bounded := layout.closed _ (List.mem_of_getElem? found)
      cases object : logical[address] <;> simp only [object, relocateObject] at moved
      all_goals
        simp only [result, run, List.map_cons, List.map_nil, relocateValue,
          dictionaryConstruct_ref logical address _ (found.trans (congrArg some object)), dictionaryConstruct_ref physical (rename address) _ moved]
      case dict entries | keyDict entries =>
        exact result_appendObject_preserves logical physical rename logicalAnchors physicalAnchors _ stack globals layout
          (by simp) (object ▸ bounded) stackInside globalsInside
      all_goals
        exact result_dictionaryFromIterable_preserves logical physical rename logicalAnchors physicalAnchors (.ref address) stack globals
          layout valueInside stackInside globalsInside
  case cons.cons =>
    cases value <;> exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
      (some (.error ⟨"TypeError", []⟩)) stack globals layout stackInside globalsInside

theorem step_dictionaryConstruct_preserves (module : Module)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.builtin .dict) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.builtin .dict) values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation (.builtin .dict) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  exact (result_dictionaryConstruct_preserves logical physical rename logicalAnchors physicalAnchors values stack globals
    layout inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_dictionaryConstruct_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (values : List Mutable.Value) (stack : List Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin logical.length (.running ⟨⟨.operation (.builtin .dict) values, stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running ⟨⟨.operation (.builtin .dict) values, stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running ⟨⟨.operation (.builtin .dict) values, stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running ⟨⟨.operation (.builtin .dict) values, stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_dictionaryConstruct_preserves module logical physical rename logicalAnchors physicalAnchors
      values stack globals layout ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
