import lang.py.FormalSW.MachineDictionaryConstruction

/-! Supported dictionary constructors allocate one fresh cell, including partial failures. -/
namespace FormalSW.PyAst.Mutable.Relocation
open HeapCalls.Relocation
set_option Elab.async false

variable {logical physical : Heap} {rename : Nat → Nat}

theorem ExecutionLayout.appendObject_result (layout : ExecutionLayout logical physical rename)
    (object : Object) (nonempty : object ≠ .tuple []) (inside : ObjectWithin logical.length object)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : appendObject object logical = some (outcome, after)) :
    let nextMap := extendMap rename logical.length physical.length
    ∃ other, appendObject (relocateObject rename object) physical = some (outcome.map (relocateValue nextMap), other) ∧
      ExecutionLayout after other nextMap ∧ after.length = logical.length + 1 ∧ other.length = physical.length + 1 ∧
      (∀ value, outcome = .ok value → value.edge.Within after.length) := by
  dsimp only
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
  refine ⟨physical ++ [relocateObject rename object], ?_, layout.append_existing object nonempty inside,
    by simp, by simp, ?_⟩
  · simp [appendObject, Except.map, relocateValue, extendMap_new]
  · intro value same
    cases same
    simp [Value.edge, Graph.Edge.Within]

theorem ExecutionLayout.dictionaryFromIterable_result (layout : ExecutionLayout logical physical rename)
    (source : Value) (inside : source.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : DictionaryConstructor.fromIterable source logical = some (outcome, after)) :
    let nextMap := extendMap rename logical.length physical.length
    ∃ other, DictionaryConstructor.fromIterable (relocateValue rename source) physical =
        some (outcome.map (relocateValue nextMap), other) ∧
      ExecutionLayout after other nextMap ∧ after.length = logical.length + 1 ∧ other.length = physical.length + 1 ∧
      (∀ value, outcome = .ok value → value.edge.Within after.length) := by
  dsimp only
  obtain ⟨result, resultHeap, other, left, right, retained, size, otherSize, bounded⟩ :=
    layout.dictionaryFromIterable source inside
  cases result with
  | none => simp only [Option.map_none, executed] at left; cases left
  | some result =>
    simp only [Option.map_some, executed, Option.some.injEq, Prod.mk.injEq] at left
    obtain ⟨rfl, rfl⟩ := left
    exact ⟨other, right, retained, size, otherSize, fun value same => bounded value (congrArg some same)⟩

theorem ExecutionLayout.dictionaryConstructAllocating (layout : ExecutionLayout logical physical rename)
    (values : List Value) (arity : values.length ≤ 1)
    (inside : ∀ value ∈ values, value.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : DictionaryConstructor.construct values logical = some (outcome, after)) :
    let nextMap := extendMap rename logical.length physical.length
    ∃ other, DictionaryConstructor.construct (values.map (relocateValue rename)) physical =
        some (outcome.map (relocateValue nextMap), other) ∧
      ExecutionLayout after other nextMap ∧ after.length = logical.length + 1 ∧ other.length = physical.length + 1 ∧
      (∀ value, outcome = .ok value → value.edge.Within after.length) := by
  dsimp only
  rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
  case nil =>
    exact layout.appendObject_result (.dict []) (by simp) (by simp [ObjectWithin, objectValues]) outcome after executed
  case cons.nil =>
    have valueInside := inside value (by simp)
    cases value with
    | scalar scalar => exact layout.dictionaryFromIterable_result (.scalar scalar) valueInside outcome after executed
    | ref address =>
      have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem valueInside
      have moved := layout.runtime.lookup address _ found
      have bounded := layout.closed _ (List.mem_of_getElem? found)
      cases object : logical[address] <;> simp only [object, relocateObject] at moved
      all_goals
        simp only [dictionaryConstruct_ref logical address _ (found.trans (congrArg some object))] at executed
        simp only [List.map_cons, List.map_nil, relocateValue, dictionaryConstruct_ref physical (rename address) _ moved]
      case dict entries | keyDict entries =>
        exact layout.appendObject_result _ (by simp) (object ▸ bounded) outcome after executed
      all_goals exact layout.dictionaryFromIterable_result (.ref address) valueInside outcome after executed
  case cons.cons => simp at arity

end FormalSW.PyAst.Mutable.Relocation
