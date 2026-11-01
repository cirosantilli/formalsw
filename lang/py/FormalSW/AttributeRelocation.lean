import lang.py.FormalSW.MachineCalls
import lang.py.FormalSW.MachineMutation

/-! Attribute access preserves nominal types, stored aliases, and method bindings. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem getAttribute_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (module : Module) (receiver : Value) (name : String)
    (inside : receiver.edge.Within logical.length) :
    getAttribute module (relocateValue rename receiver) name physical =
      (getAttribute module receiver name logical).map
        (fun result => (result.1.map (relocateValue rename), physical)) := by
  cases receiver with
  | scalar value => simp [getAttribute, relocateValue, Mutable.unsupported]
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    change getAttribute module (.ref (rename address)) name physical = _
    cases object : logical[address] with
    | «instance» origin className fields | dataInstance origin className frozen declared fields =>
      simp only [object, relocateObject] at moved
      cases definition : module.findClass className with
      | none => simp [getAttribute, relocateValue, found, object, moved, instanceClass, definition, Mutable.unsupported]
      | some pair =>
        rcases pair with ⟨identity, body⟩
        by_cases nominal : identity = origin
        · by_cases special : name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__"
          · simp [getAttribute, relocateValue, found, object, moved, instanceClass, definition,
              nominal, special, Mutable.unsupported]
          · cases field : fields.lookup name with
            | some value =>
              simp [getAttribute, found, object, moved, instanceClass, definition,
                nominal, special, fields_lookup_relocate, field, Except.map]
            | none =>
              by_cases missing : (findFunctionIn body name).isSome = true ∨ ['_', '_'] <+: name.toList <;>
                simp [getAttribute, found, object, moved, instanceClass, definition,
                  nominal, special, fields_lookup_relocate, field, missing, Mutable.unsupported, Mutable.error, Except.map]
        · simp [getAttribute, relocateValue, found, object, moved, instanceClass, definition, nominal, Mutable.unsupported]
    | list items | tuple items | bytearray bytes | set items | keySet items | dict entries | keyDict entries =>
      simp only [object, relocateObject] at moved
      simp [getAttribute, relocateValue, found, object, moved, Mutable.unsupported]

/-- Completed attribute access agrees with field access after the class checks have passed. -/
theorem getAttribute_readField (module : Module) (heap after : Mutable.Heap) (receiver : Value)
    (name : String) (outcome : Except ExceptionObject Value)
    (executed : getAttribute module receiver name heap = some (outcome, after)) :
    Mutable.readField receiver name heap = some (outcome, after) := by
  cases receiver with
  | scalar value => simp [getAttribute, Mutable.unsupported] at executed
  | ref address =>
    cases found : heap[address]? with
    | none => simp [getAttribute, found, Mutable.unsupported] at executed
    | some object =>
      cases object with
      | «instance» origin className fields | dataInstance origin className frozen declared fields =>
        cases definition : module.findClass className with
        | none => simp [getAttribute, found, instanceClass, definition, Mutable.unsupported] at executed
        | some pair =>
          rcases pair with ⟨identity, body⟩
          by_cases nominal : identity = origin
          · by_cases special : name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__"
            · simp [getAttribute, found, instanceClass, definition, nominal, special, Mutable.unsupported] at executed
            · cases field : fields.lookup name with
              | some value =>
                simpa [Mutable.readField, Mutable.instanceData, found, special, field] using
                  (show some (.ok value, heap) = some (outcome, after) from by
                    simpa [getAttribute, found, instanceClass, definition, nominal, special, field] using executed)
              | none =>
                by_cases missing : (findFunctionIn body name).isSome = true ∨ ['_', '_'] <+: name.toList
                · simp [getAttribute, found, instanceClass, definition, nominal, special, field,
                    missing, Mutable.unsupported] at executed
                · simpa [Mutable.readField, Mutable.instanceData, found, special, field, Mutable.error] using
                    (show some (.error {typeName := "AttributeError", args := []}, heap) = some (outcome, after) from by
                      simpa [getAttribute, found, instanceClass, definition, nominal, special, field,
                        missing, Mutable.error] using executed)
          · simp [getAttribute, found, instanceClass, definition, nominal, Mutable.unsupported] at executed
      | list items | tuple items | bytearray bytes | set items | keySet items | dict entries | keyDict entries =>
        simp [getAttribute, found, Mutable.unsupported] at executed

theorem step_attribute_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (receiver : Value) (name : String) (stack : List Frame) (globals : Mutable.Globals)
    (receiverInside : receiver.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals)
    (outcome : Except ExceptionObject Value) (after : Mutable.Heap)
    (executed : getAttribute module receiver name logical = some (outcome, after)) :
    after = logical ∧
      step module physicalAnchors (relocateState rename physical ⟨.value receiver, .attribute name :: stack, logical⟩)
          (relocateGlobals rename globals) =
        relocateStep rename physical physicalAnchors
          (step module logicalAnchors ⟨.value receiver, .attribute name :: stack, logical⟩ globals) ∧
      StepWithin (step module logicalAnchors ⟨.value receiver, .attribute name :: stack, logical⟩ globals) := by
  have effect := layout.readField receiver name receiverInside outcome after
    (getAttribute_readField module logical after receiver name outcome executed)
  have same := effect.2.2.1
  subst after
  have paired := getAttribute_relocates logical physical rename layout.runtime module receiver name receiverInside
  rw [executed] at paired
  refine ⟨rfl, ?_, ?_⟩
  · have transported := result_relocates rename logical physical logical physical logicalAnchors physicalAnchors
      (getAttribute module receiver name) (getAttribute module (relocateValue rename receiver) name)
      stack globals outcome executed paired
    simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step]
    rw [transported]
    simpa only [List.map_cons, relocateFrame] using
      protectGenerator_relocates rename physical physicalAnchors (.attribute name :: stack) _
  · apply protectGenerator_within
    exact result_within logicalAnchors logical logical _ stack globals outcome executed (Nat.le_refl _)
      effect.2.2.2 stackInside globalsInside

theorem bindMethod_scalar_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (module : Module) (value : Constant) (name : String) (ordinary : name ≠ "$formalsw.sort.reverse") :
    bindMethod module (.scalar value) name physical =
      (bindMethod module (.scalar value) name logical).map
        (fun result => (result.1.map (relocateOperation rename), physical)) := by
  by_cases isdigitName : name = "isdigit"
  · subst name; cases value <;> rfl
  by_cases upperName : name = "upper"
  · subst name; cases value <;> rfl
  by_cases stripName : name = "strip"
  · subst name; cases value <;> rfl
  by_cases splitName : name = "split"
  · subst name; cases value <;> rfl
  by_cases replaceName : name = "replace"
  · subst name; cases value <;> rfl
  by_cases zfillName : name = "zfill"
  · subst name; cases value <;> rfl
  by_cases joinName : name = "join"
  · subst name; cases value <;> rfl
  by_cases countName : name = "count"
  · subst name; cases value <;> rfl
  by_cases appendName : name = "append"
  · subst name; cases value <;> rfl
  by_cases addName : name = "add"
  · subst name; cases value <;> rfl
  by_cases getName : name = "get"
  · subst name; cases value <;> rfl
  by_cases setdefaultName : name = "setdefault"
  · subst name; cases value <;> rfl
  by_cases popName : name = "pop"
  · subst name; cases value <;> rfl
  by_cases sortName : name = "sort"
  · subst name; cases value <;> rfl
  simp [bindMethod, ordinary, isdigitName, upperName, stripName, splitName, replaceName,
    zfillName, joinName, countName, appendName, addName, getName, setdefaultName, popName, sortName, Mutable.unsupported]

set_option maxHeartbeats 400000 in
theorem bindMethod_builtin_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (module : Module) (address : Nat) (object : Mutable.Object) (name : String)
    (found : logical[address]? = some object)
    (moved : physical[rename address]? = some (relocateObject rename object))
    (builtin : match object with | .instance _ _ _ | .dataInstance _ _ _ _ _ => False | _ => True)
    (ordinary : name ≠ "$formalsw.sort.reverse") :
    bindMethod module (.ref (rename address)) name physical =
      (bindMethod module (.ref address) name logical).map
        (fun result => (result.1.map (relocateOperation rename), physical)) := by
  by_cases sortName : name = "sort"
  · subst name
    cases object <;> try contradiction
    all_goals simp only [relocateObject] at moved
    all_goals simp [bindMethod, found, moved, Mutable.error, Except.map, relocateOperation, relocateValue]
    all_goals rfl
  by_cases appendName : name = "append"
  · subst name
    cases object <;> try contradiction
    all_goals simp only [relocateObject] at moved
    all_goals simp [bindMethod, found, moved, Mutable.error, Except.map, relocateOperation, relocateValue]
    all_goals rfl
  by_cases popName : name = "pop"
  · subst name
    cases object <;> try contradiction
    all_goals simp only [relocateObject] at moved
    all_goals simp [bindMethod, found, moved, Mutable.error, Except.map, relocateOperation, relocateValue]
    all_goals rfl
  by_cases countName : name = "count"
  · subst name
    cases object <;> try contradiction
    all_goals simp only [relocateObject] at moved
    all_goals simp [bindMethod, found, moved, Mutable.error, Except.map, relocateOperation, relocateValue]
    all_goals rfl
  by_cases getName : name = "get"
  · subst name
    cases object <;> try contradiction
    all_goals simp only [relocateObject] at moved
    all_goals simp [bindMethod, found, moved, Mutable.error, Except.map, relocateOperation, relocateValue]
    all_goals rfl
  by_cases setdefaultName : name = "setdefault"
  · subst name
    cases object <;> try contradiction
    all_goals simp only [relocateObject] at moved
    all_goals simp [bindMethod, found, moved, Mutable.error, Except.map, relocateOperation, relocateValue]
    all_goals rfl
  by_cases isdigitName : name = "isdigit"
  · subst name
    cases object <;> try contradiction
    all_goals simp only [relocateObject] at moved
    all_goals simp [bindMethod, found, moved, Mutable.error, Except.map, relocateOperation, relocateValue]
    all_goals rfl
  by_cases upperName : name = "upper"
  · subst name
    cases object <;> try contradiction
    all_goals simp only [relocateObject] at moved
    all_goals simp [bindMethod, found, moved, Mutable.error, Except.map, relocateOperation, relocateValue]
    all_goals rfl
  by_cases stripName : name = "strip"
  · subst name
    cases object <;> try contradiction
    all_goals simp only [relocateObject] at moved
    all_goals simp [bindMethod, found, moved, Mutable.error, Except.map, relocateOperation, relocateValue]
    all_goals rfl
  by_cases splitName : name = "split"
  · subst name
    cases object <;> try contradiction
    all_goals simp only [relocateObject] at moved
    all_goals simp [bindMethod, found, moved, Mutable.error, Except.map, relocateOperation, relocateValue]
    all_goals rfl
  by_cases zfillName : name = "zfill"
  · subst name
    cases object <;> try contradiction
    all_goals simp only [relocateObject] at moved
    all_goals simp [bindMethod, found, moved, Mutable.error, Except.map, relocateOperation, relocateValue]
    all_goals rfl
  by_cases replaceName : name = "replace"
  · subst name
    cases object <;> try contradiction
    all_goals simp only [relocateObject] at moved
    all_goals simp [bindMethod, found, moved, Mutable.error, Except.map, relocateOperation, relocateValue]
    all_goals rfl
  by_cases addName : name = "add"
  · subst name
    cases object <;> try contradiction
    all_goals simp only [relocateObject] at moved
    all_goals simp [bindMethod, found, moved, Mutable.error, Except.map, relocateOperation, relocateValue]
    all_goals rfl
  by_cases clearName : name = "clear"
  · subst name
    cases object <;> try contradiction
    all_goals simp only [relocateObject] at moved
    all_goals simp [bindMethod, found, moved, Mutable.error, Except.map, relocateOperation, relocateValue]
    all_goals rfl
  cases object <;> try contradiction
  all_goals simp only [relocateObject] at moved
  all_goals simp [bindMethod, found, moved, ordinary, sortName, appendName, popName, countName,
    getName, setdefaultName, isdigitName, upperName, stripName, splitName, zfillName, replaceName,
    addName, clearName, Mutable.unsupported]

theorem bindMethod_ordinary_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (module : Module) (receiver : Value) (name : String)
    (inside : receiver.edge.Within logical.length) (ordinary : name ≠ "$formalsw.sort.reverse") :
    bindMethod module (relocateValue rename receiver) name physical =
      (bindMethod module receiver name logical).map
        (fun result => (result.1.map (relocateOperation rename), physical)) := by
  cases receiver with
  | scalar value => exact bindMethod_scalar_relocates logical physical rename module value name ordinary
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    change bindMethod module (.ref (rename address)) name physical = _
    cases object : logical[address] with
    | «instance» origin className fields | dataInstance origin className frozen declared fields =>
      simp only [object, relocateObject] at moved
      cases definition : module.findClass className with
      | none => simp [bindMethod, ordinary, found, object, moved, instanceClass, definition, Mutable.unsupported]
      | some pair =>
        rcases pair with ⟨identity, body⟩
        by_cases nominal : identity = origin
        · by_cases special : name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__"
          · simp [bindMethod, ordinary, found, object, moved, instanceClass, definition, nominal, special, Mutable.unsupported]
          · cases field : fields.lookup name with
            | some value =>
              simp [bindMethod, ordinary, found, object, moved, instanceClass, definition,
                nominal, special, fields_lookup_relocate, field, Except.map, relocateOperation]
            | none =>
              cases method : findFunctionIn body name with
              | some pair =>
                rcases pair with ⟨args, methodBody⟩
                simp [bindMethod, ordinary, found, object, moved, instanceClass, definition,
                  nominal, special, fields_lookup_relocate, field, method, Except.map, relocateOperation]
                rfl
              | none =>
                by_cases missing : ['_', '_'] <+: name.toList <;>
                  simp [bindMethod, ordinary, found, object, moved, instanceClass, definition,
                    nominal, special, fields_lookup_relocate, field, method, missing, Mutable.unsupported, Mutable.error, Except.map]
        · simp [bindMethod, ordinary, found, object, moved, instanceClass, definition, nominal, Mutable.unsupported]
    | list items | tuple items | bytearray bytes | set items | keySet items | dict entries | keyDict entries =>
      exact bindMethod_builtin_relocates logical physical rename module address _ name
        found moved (by simp [object]) ordinary

end FormalSW.PyAst.HeapCalls.Relocation
