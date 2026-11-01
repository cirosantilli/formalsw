import lang.py.FormalSW.MachineConstructionInvariant
import lang.py.FormalSW.MachineAttributes

/-! Constructor dispatch preserves fresh instances, argument errors and caller references. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_allocateInstance_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (origin name : String) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.allocateInstance origin name) stack globals)
      (result physicalAnchors physical (Mutable.allocateInstance origin name)
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  apply result_preserves logical physical (logical ++ [.instance origin name []])
    (physical ++ [.instance origin name []]) rename (extendMap rename logical.length physical.length)
    logicalAnchors physicalAnchors _ _ stack globals (.ok (.ref logical.length))
    (extendMap_old rename logical.length physical.length) (by simp) (by simp)
    (layout.append_existing (.instance origin name []) (by simp) (by simp [ObjectWithin, objectValues]))
    stackInside globalsInside
  · intro value same
    cases same
    simp [Mutable.Value.edge, Graph.Edge.Within]
  · rfl
  · simp [Mutable.allocateInstance_result, Except.map, relocateValue, extendMap_new]

theorem result_allocateDataclass_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (origin name : String) (frozen : Bool)
    (declared : List String) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.allocateDataclass origin name frozen declared values) stack globals)
      (result physicalAnchors physical
        (Mutable.allocateDataclass origin name frozen declared (values.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  by_cases arity : declared.length = values.length
  · have bounded : ObjectWithin logical.length (.dataInstance origin name frozen declared (declared.zip values)) := by
      intro value member
      change value ∈ (declared.zip values).map Prod.snd at member
      obtain ⟨pair, pairedMember, equal⟩ := List.mem_map.mp member
      rw [← equal]
      exact valuesInside pair.2 (List.of_mem_zip pairedMember).2
    have mapped : (declared.zip values).map (fun pair => (pair.1, relocateValue rename pair.2)) =
        declared.zip (values.map (relocateValue rename)) := by
      clear valuesInside arity bounded
      induction declared generalizing values with
      | nil => rfl
      | cons field fields ih => cases values <;> simp [ih]
    have retained := layout.append_existing (.dataInstance origin name frozen declared (declared.zip values))
      (by simp) bounded
    simp only [relocateObject, mapped] at retained
    apply result_preserves logical physical _ _ rename (extendMap rename logical.length physical.length)
      logicalAnchors physicalAnchors _ _ stack globals (.ok (.ref logical.length))
      (extendMap_old rename logical.length physical.length) (by simp) (by simp) retained stackInside globalsInside
    · intro value same
      cases same
      simp [Mutable.Value.edge, Graph.Edge.Within]
    · exact Mutable.allocateDataclass_result origin name frozen declared values logical arity
    · simpa only [Except.map, relocateValue, extendMap_new] using
        Mutable.allocateDataclass_result origin name frozen declared (values.map (relocateValue rename)) physical
          (by simpa using arity)
  · apply result_preserves logical physical logical physical rename rename logicalAnchors physicalAnchors
      _ _ stack globals (.error ⟨"TypeError", []⟩) (fun _ _ => rfl) (Nat.le_refl _) (Nat.le_refl _)
      layout stackInside globalsInside
    · intro value impossible
      cases impossible
    · simp [Mutable.allocateDataclass, arity, Mutable.error]
    · simp [Mutable.allocateDataclass, arity, Mutable.error, Except.map]

/-- Allocation precedes argument validation, including an initializer with the wrong arity. -/
theorem invoke_fresh_instance_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (origin name : String) (args : List Arg) (body : List Stmt)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (source : ∀ statement ∈ body, StmtWithin 0 statement)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (invokeMethod logicalAnchors (.ref logical.length) args body values (.initialized logical.length :: stack)
        (logical ++ [.instance origin name []]) globals)
      (invokeMethod physicalAnchors (.ref physical.length) args body (values.map (relocateValue rename))
        (.initialized physical.length :: stack.map (relocateFrame rename))
        (physical ++ [.instance origin name []]) (relocateGlobals rename globals)) := by
  let nextMap := extendMap rename logical.length physical.length
  have agree : ∀ address < logical.length, nextMap address = rename address := extendMap_old _ _ _
  have larger : logical.length ≤ (logical ++ [Mutable.Object.instance origin name []]).length := by simp
  have newGlobals := globalsInside.mono larger
  refine ⟨logical ++ [.instance origin name []], physical ++ [.instance origin name []], nextMap,
    agree, larger, by simp,
    layout.append_existing (.instance origin name []) (by simp) (by simp [ObjectWithin, objectValues]), ?_, ?_, ?_⟩
  · cases completed : completeArguments args (.ref logical.length :: values) <;>
      simp [invokeMethod, completed, done, StepHeap]
  · cases completed : completeArguments args (.ref logical.length :: values) with
    | none =>
      simpa only [invokeMethod, completed] using
        (show StepWithin (done logicalAnchors (logical ++ [.instance origin name []])
          (.error ⟨"TypeError", []⟩) globals) from ⟨newGlobals, by intro value impossible; cases impossible⟩)
    | some filled =>
      simp only [invokeMethod, completed]
      exact invokeMethod_within _ logicalAnchors (.ref logical.length) args body values
        (.initialized logical.length :: stack) globals _ (by simp [Mutable.Value.edge, Graph.Edge.Within])
        (fun value member => valueWithin_mono _ _ value larger (valuesInside value member))
        (fun statement member => (source statement member).mono (Nat.zero_le _))
        (by intro frame member; rcases List.mem_cons.mp member with rfl | member
            · simp [FrameWithin]
            · exact (stackInside frame member).mono larger)
        newGlobals (by simp only [invokeMethod, completed])
  · have paired := invokeMethod_relocate nextMap (logical ++ [.instance origin name []])
      (physical ++ [.instance origin name []]) logicalAnchors physicalAnchors (.ref logical.length) args body values
      (.initialized logical.length :: stack) globals
    have valuesSame : values.map (relocateValue nextMap) = values.map (relocateValue rename) := by
      apply List.map_congr_left
      intro value member
      exact relocateValue_congr nextMap rename logical.length value agree (valuesInside value member)
    simpa only [relocateValue, nextMap, extendMap_new, relocateBody_source _ body source,
      List.map_cons, relocateFrame, relocateStack_congr _ rename logical.length stack agree stackInside,
      relocateGlobals_congr _ rename logical.length globals agree globalsInside, valuesSame] using paired

/-- All modeled class lookups, generated constructors and initializer entries. -/
theorem construct_preserves (module : Module) (name : String)
    (source : ∀ statement ∈ module.body, StmtWithin 0 statement)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (construct module logicalAnchors name values stack logical globals)
      (construct module physicalAnchors name (values.map (relocateValue rename))
        (stack.map (relocateFrame rename)) physical (relocateGlobals rename globals)) := by
  cases selected : module.findClass name with
  | none =>
    apply Preserves.unchanged layout
    · simp [construct, selected, StepHeap]
    · simp [construct, selected, StepWithin]
    · simp [construct, selected, relocateStep]
  | some definition =>
    rcases definition with ⟨origin, classBody⟩
    cases initialized : findFunctionIn classBody "__init__" with
    | some definition =>
      rcases definition with ⟨args, body⟩
      simp only [construct, selected, initialized]
      exact invoke_fresh_instance_preserves logical physical rename logicalAnchors physicalAnchors origin name
        args body values stack globals layout
        (findFunctionIn_within 0 classBody "__init__" args body
          (findClass_within 0 module name origin classBody source selected) initialized)
        valuesInside stackInside globalsInside
    | none =>
      cases generated : dataclassFields classBody with
      | some fields =>
        rcases fields with ⟨frozen, fields⟩
        simp only [construct, selected, initialized, generated]
        exact result_allocateDataclass_preserves logical physical rename logicalAnchors physicalAnchors
          origin name frozen (fields.map Arg.name) values stack globals layout valuesInside stackInside globalsInside
      | none =>
        cases values with
        | nil =>
          simp only [construct, selected, initialized, generated, List.isEmpty_nil, List.map_nil, if_true]
          exact result_allocateInstance_preserves logical physical rename logicalAnchors physicalAnchors
            origin name stack globals layout stackInside globalsInside
        | cons value rest =>
          apply Preserves.unchanged layout
          · simp [construct, selected, initialized, generated, done, StepHeap]
          · simpa only [construct, selected, initialized, generated, List.isEmpty_cons, Bool.false_eq_true, if_false] using
              (show StepWithin (done logicalAnchors logical (.error ⟨"TypeError", []⟩) globals) from
                ⟨globalsInside, by intro value impossible; cases impossible⟩)
          · simp [construct, selected, initialized, generated, done, relocateStep, relocateCompletion, Except.map]

theorem step_constructor_preserves (module : Module) (name : String)
    (source : ∀ statement ∈ module.body, StmtWithin 0 statement)
    (functionMissing : findFunctionIn module.body name = none)
    (libraryMissing : libraryFunction module name = none)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.call name) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.call name) values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation (.call name) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  simpa only [step, relocateState, relocateWork, relocateRuntimeOperation, relocateOperation,
    functionMissing, libraryMissing] using
    (construct_preserves module name source logical physical rename logicalAnchors physicalAnchors
      values stack globals layout inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation
