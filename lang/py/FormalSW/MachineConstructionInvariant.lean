import lang.py.FormalSW.MachineMutationInvariant
import lang.py.FormalSW.ConstructionRelocation

/-! Tuple and dictionary displays retain the execution invariant across allocation. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem step_tuple_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (items : List Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation .tuple items, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation .tuple items, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation .tuple items, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  obtain ⟨address, otherAddress, after, other, nextMap, first, second, retained, bounded, same, agree⟩ :=
    layout.allocateTuple items inside.1.2
  have moved : Mutable.allocateTuple (items.map (relocateValue rename)) physical =
      some ((Except.ok (.ref address)).map (relocateValue nextMap), other) := by
    simpa only [Except.map, relocateValue, same] using second
  exact (result_preserves logical physical after other rename nextMap logicalAnchors physicalAnchors
    (Mutable.allocateTuple items) (Mutable.allocateTuple (items.map (relocateValue rename))) stack globals
    (.ok (.ref address)) agree
    (allocateTuple_length logical after items (.ref address) first)
    (allocateTuple_length physical other _ (.ref otherAddress) second) retained inside.2 globalsInside
    (by intro value equal; cases equal; exact bounded) first moved).protectGenerator stack inside.2

theorem step_tuple_expression_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (items : List Expr) (env : Env) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.tuple items) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.tuple items) env, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.expr (.tuple items) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · cases items <;> rfl
  · exact argumentsState_within logical .tuple env [] items stack (by trivial) inside.1 (by simp) inside.2
  · cases items <;> simp [step, argumentsState, relocateState, relocateWork, relocateFrame,
      relocateRuntimeOperation, relocateOperation, relocateStep]

theorem step_dictionary_expression_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (items : List (Expr × Expr)) (env : Env) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.dict items) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.dict items) env, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.expr (.dict items) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · rfl
  · exact ⟨⟨inside.1, by simp⟩, inside.2⟩
  · rfl

theorem step_dictionary_entry_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (key value : Expr) (rest : List (Expr × Expr))
    (entries : List (Constant × Value)) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.dictionary ((key, value) :: rest) entries env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.dictionary ((key, value) :: rest) entries env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.dictionary ((key, value) :: rest) entries env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨inside.1.1, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [FrameWithin] using inside.1
    · exact inside.2 frame member
  · simp [step, relocateState, relocateWork, relocateFrame, relocateStep]

/-- A singleton retains its reference key while the value expression runs. -/
theorem step_dictionaryKey_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (key : Value) (value : Expr) (rest : List (Expr × Expr))
    (entries : List (Constant × Value)) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value key, .dictionaryKey value rest entries env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value key, .dictionaryKey value rest entries env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value key, .dictionaryKey value rest entries env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have saved := inside.2 (.dictionaryKey value rest entries env) (by simp)
  simp only [FrameWithin] at saved
  apply Preserves.unchanged layout
  · cases key <;> cases rest <;> cases entries <;> simp [step, StepHeap, protectGenerator]
  · cases key with
    | ref address =>
      cases rest <;> cases entries
      all_goals try trivial
      refine ⟨saved.1, ?_⟩
      intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · simp only [FrameWithin, OperationWithin]
        exact ⟨saved.1, by trivial, by simpa using inside.1⟩
      · exact inside.2 frame (by simp [member])
    | scalar scalar =>
      refine ⟨saved.1, ?_⟩
      intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · simpa only [FrameWithin] using saved
      · exact inside.2 frame (by simp [member])
  · cases key <;> cases rest <;> cases entries <;>
      simp [step, relocateState, relocateWork, relocateFrame, relocateValue, relocateStep,
        relocateRuntimeOperation, relocateOperation, protectGenerator]

/-- Duplicate keys keep their original representative while the latest value replaces the old one. -/
theorem step_dictionaryValue_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (key : Constant) (rest : List (Expr × Expr))
    (entries : List (Constant × Value)) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .dictionaryValue key rest entries env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .dictionaryValue key rest entries env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .dictionaryValue key rest entries env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have saved := inside.2 (.dictionaryValue key rest entries env) (by simp)
  simp only [FrameWithin] at saved
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨⟨saved.1, ?_⟩, fun frame member => inside.2 frame (by simp [member])⟩
    have inserted := ScalarDict.insert_property entries key value (fun _ => True)
      (fun item => item.edge.Within logical.length)
      (fun entry member => ⟨trivial, saved.2 entry member⟩) trivial inside.1
    exact fun entry member => (inserted entry member).2
  · simp only [step, relocateState, relocateWork, relocateFrame, List.map_cons, scalarDict_insert_relocates,
      protectGenerator_next, relocateStep]

theorem step_dictionary_finish_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (entries : List (Constant × Value)) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.dictionary [] entries env, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.dictionary [] entries env, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.dictionary [] entries env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have bounded : ObjectWithin logical.length (.dict entries) := by
    intro value member
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    exact inside.1.2 entry present
  obtain ⟨first, second, retained⟩ := layout.allocateDict entries bounded
  have moved : Mutable.allocateDict (entries.map fun entry => (entry.1, relocateValue rename entry.2)) physical =
      some ((Except.ok (.ref logical.length)).map (relocateValue (extendMap rename logical.length physical.length)),
        physical ++ [.dict (entries.map fun entry => (entry.1, relocateValue rename entry.2))]) := by
    simpa only [Except.map, relocateValue, extendMap_new] using second
  exact (result_preserves logical physical _ _ rename (extendMap rename logical.length physical.length)
    logicalAnchors physicalAnchors _ _ stack globals (.ok (.ref logical.length))
    (extendMap_old rename logical.length physical.length) (by simp) (by simp) retained inside.2 globalsInside
    (by intro value equal; cases equal; simp [Mutable.Value.edge, Graph.Edge.Within]) first moved).protectGenerator stack inside.2

theorem step_dictionary_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (expressions : List (Expr × Expr))
    (entries : List (Constant × Value)) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.dictionary expressions entries env, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.dictionary expressions entries env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.dictionary expressions entries env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases expressions with
  | nil =>
    exact step_dictionary_finish_preserves module logical physical rename logicalAnchors physicalAnchors
      entries env stack globals layout inside globalsInside
  | cons entry rest =>
    rcases entry with ⟨key, value⟩
    exact step_dictionary_entry_preserves module logical physical rename logicalAnchors physicalAnchors
      key value rest entries env stack globals layout inside

end FormalSW.PyAst.HeapCalls.Relocation
