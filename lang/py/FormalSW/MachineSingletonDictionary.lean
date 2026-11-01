import lang.py.FormalSW.MachineDictionaryConstruction

/-! Singleton displays retain shared keys and values across heap relocation. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem step_dictionarySingleton_preserves (module : Module)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (key value : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation .dictionarySingleton [key, value], stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation .dictionarySingleton [key, value], stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation .dictionarySingleton [key, value], stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have keyInside := inside.1.2 key (by simp)
  have valueInside := inside.1.2 value (by simp)
  have normalized (key value : Value) : DictionaryDisplay.singleton key value =
      (do let hashed ← Mutable.hashKey key; appendObject (.keyDict [(hashed, key, value)])) := by
    funext heap
    rfl
  change Preserves logical physical rename physicalAnchors
    (protectGenerator stack (result logicalAnchors logical (DictionaryDisplay.singleton key value) stack globals))
    (protectGenerator (stack.map (relocateFrame rename))
      (result physicalAnchors physical (DictionaryDisplay.singleton (relocateValue rename key) (relocateValue rename value))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)))
  apply Preserves.protectGenerator _ stack inside.2
  rw [normalized, normalized, result_bind, result_bind]
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ id _ _ globals
    layout globalsInside
  · intro outcome after executed
    cases selected : Mutable.keyOf logical key with
    | none => simp [Mutable.hashKey, selected] at executed
    | some result =>
        simp only [Mutable.hashKey, selected, Option.map_some, Option.some.injEq, Prod.mk.injEq] at executed
        exact executed.2.symm
  · simpa using layout.hashKey key keyInside
  · intro hashed _
    have bounded : ObjectWithin logical.length (.keyDict [(hashed, key, value)]) := by
      simpa [ObjectWithin, objectValues] using And.intro keyInside valueInside
    exact result_appendObject_preserves logical physical rename logicalAnchors physicalAnchors
      (.keyDict [(hashed, key, value)]) stack globals layout (by simp) bounded inside.2 globalsInside

end FormalSW.PyAst.HeapCalls.Relocation
