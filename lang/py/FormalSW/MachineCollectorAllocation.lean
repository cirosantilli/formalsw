import lang.py.FormalSW.MachineGeneratorAcquisition

/-! Collector allocation reserves a fresh address without changing existing caller references. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

theorem ExecutionLayout.congr {logical physical : Heap} {rename other : Nat → Nat}
    (layout : ExecutionLayout logical physical rename)
    (agree : ∀ address < logical.length, other address = rename address) :
    ExecutionLayout logical physical other := by
  refine ⟨⟨?_, ?_⟩, layout.closed, ?_⟩
  · intro left leftInside right rightInside same
    exact layout.runtime.injective left leftInside right rightInside
      (by simpa only [agree left leftInside, agree right rightInside] using same)
  · intro address object found
    have inside := (List.getElem?_eq_some_iff.mp found).1
    rw [agree address inside, relocateObject_congr other rename logical.length object agree
      (layout.closed object (List.mem_of_getElem? found))]
    exact layout.runtime.lookup address object found
  · intro address found
    rw [agree address (List.getElem?_eq_some_iff.mp (emptyTupleAddress_lookup found)).1]
    exact layout.interned address found

end FormalSW.PyAst.Mutable.Relocation

namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- Only addresses present before the step constrain its initial map. -/
theorem Preserves.congr_initial {logical physical : Mutable.Heap} {rename other : Nat → Nat} {anchors : Nat}
    {left right : Step State Mutable.Completion}
    (preserved : Preserves logical physical rename anchors left right)
    (agree : ∀ address < logical.length, other address = rename address) :
    Preserves logical physical other anchors left right := by
  obtain ⟨after, physicalAfter, nextMap, retained, rest⟩ := preserved
  exact ⟨after, physicalAfter, nextMap, fun address inside => (retained address inside).trans (agree address inside).symm, rest⟩

def collectorObject (isSet : Bool) (dictionaryValue : Option Expr) : Mutable.Object :=
  if dictionaryValue.isSome then .dict [] else if isSet then .set [] else .list []

def collectorTerminal (address : Nat) (element : Expr) (isSet : Bool) : Option Expr → Stmt
  | some value => .comprehensionStore address element value
  | none => if isSet then .comprehensionAdd address element else .comprehensionAppend address element

def collectorEnter (isSet : Bool) (dictionaryValue : Option Expr) (env : Env) (stack : List Frame)
    (loop : Stmt) (heap : Mutable.Heap) : Step State Mutable.Completion :=
  .next ⟨.block [loop] env, .comprehensionResult heap.length :: stack, heap ++ [collectorObject isSet dictionaryValue]⟩

theorem collectorObject_relocates (rename : Nat → Nat) (isSet : Bool) (dictionaryValue : Option Expr) :
    relocateObject rename (collectorObject isSet dictionaryValue) = collectorObject isSet dictionaryValue := by
  cases dictionaryValue <;> cases isSet <;> rfl

theorem collectorTerminal_relocates (rename : Nat → Nat) (address : Nat) (element : Expr)
    (isSet : Bool) (dictionaryValue : Option Expr) :
    relocateStmt rename (collectorTerminal address element isSet dictionaryValue) =
      collectorTerminal (rename address) element isSet dictionaryValue := by
  cases dictionaryValue <;> cases isSet <;> simp [collectorTerminal, relocateStmt]

theorem collectorTerminal_within (limit address : Nat) (element : Expr) (isSet : Bool)
    (dictionaryValue : Option Expr) (inside : address < limit) :
    StmtWithin limit (collectorTerminal address element isSet dictionaryValue) := by
  cases dictionaryValue <;> cases isSet <;> simpa [collectorTerminal, StmtWithin] using inside

theorem collectorEnter_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat) (anchors : Nat)
    (isSet : Bool) (dictionaryValue : Option Expr) (env : Env) (stack : List Frame) (loop : Stmt)
    (layout : ExecutionLayout logical physical rename) (envInside : EnvWithin logical.length env)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (loopInside : StmtWithin (logical.length + 1) loop) :
    Preserves logical physical rename anchors
      (collectorEnter isSet dictionaryValue env stack loop logical)
      (collectorEnter isSet dictionaryValue (relocateEnv rename env) (stack.map (relocateFrame rename))
        (relocateStmt (extendMap rename logical.length physical.length) loop) physical) := by
  let nextMap := extendMap rename logical.length physical.length
  have agree : ∀ address < logical.length, nextMap address = rename address := extendMap_old _ _ _
  have larger : logical.length ≤ (logical ++ [collectorObject isSet dictionaryValue]).length := by simp
  have retained := layout.append_existing (collectorObject isSet dictionaryValue)
    (by cases dictionaryValue <;> cases isSet <;> simp [collectorObject])
    (by cases dictionaryValue <;> cases isSet <;> simp [collectorObject, ObjectWithin, objectValues])
  rw [collectorObject_relocates] at retained
  refine ⟨logical ++ [collectorObject isSet dictionaryValue], physical ++ [collectorObject isSet dictionaryValue],
    nextMap, agree, larger, by simp, retained, rfl, ?_, ?_⟩
  · refine ⟨⟨envInside.mono larger, ?_⟩, ?_⟩
    · simpa using loopInside
    · intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · simp [FrameWithin]
      · exact (stackInside frame member).mono larger
  · simp only [collectorEnter, relocateStep, relocateState, relocateWork, List.map_cons, List.map_nil,
      relocateFrame, nextMap, extendMap_new,
      relocateEnv_congr nextMap rename logical.length env agree envInside,
      relocateStack_congr nextMap rename logical.length stack agree stackInside]

theorem collectorAcquireBody_preserves (kind : GeneratorSource) (target : Expr) (body : Nat → List Stmt) (isSet : Bool) (dictionaryValue : Option Expr)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (env : Env) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (envInside : EnvWithin logical.length env)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals)
    (bounded : ∀ statement ∈ body logical.length, StmtWithin (logical.length + 1) statement)
    (moved : (body logical.length).map (relocateStmt (extendMap rename logical.length physical.length)) = body physical.length) :
    Preserves logical physical rename physicalAnchors
      (generatorAcquire logicalAnchors kind false target
        (body logical.length)
        values logical globals (collectorEnter isSet dictionaryValue env stack))
      (generatorAcquire physicalAnchors kind false target
        (body physical.length)
        (values.map (relocateValue rename)) physical (relocateGlobals rename globals)
        (collectorEnter isSet dictionaryValue (relocateEnv rename env) (stack.map (relocateFrame rename)))) := by
  let nextMap := extendMap rename logical.length physical.length
  have agree : ∀ address < logical.length, nextMap address = rename address := extendMap_old _ _ _
  have valuesSame : values.map (relocateValue nextMap) = values.map (relocateValue rename) := by
    apply List.map_congr_left
    intro value member
    exact relocateValue_congr nextMap rename logical.length value agree (valuesInside value member)
  have preserved := generatorAcquire_preserves_at kind false target logical physical nextMap
    logicalAnchors physicalAnchors (logical.length + 1) (Nat.le_succ _) (body logical.length) values globals
    (collectorEnter isSet dictionaryValue env stack)
    (collectorEnter isSet dictionaryValue (relocateEnv rename env) (stack.map (relocateFrame rename)))
    (layout.congr agree) bounded valuesInside globalsInside (by
      intro loop loopInside
      exact (collectorEnter_preserves logical physical rename physicalAnchors isSet dictionaryValue env stack loop
        layout envInside stackInside loopInside).congr_initial agree)
  rw [moved, valuesSame, relocateGlobals_congr nextMap rename logical.length globals agree globalsInside] at preserved
  exact preserved.congr_initial (fun address inside => (agree address inside).symm)

theorem collectorAcquire_preserves (kind : GeneratorSource) (target element : Expr) (filters : List Expr)
    (rest : List (Expr × Expr × List Expr)) (isSet : Bool) (dictionaryValue : Option Expr)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (env : Env) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (envInside : EnvWithin logical.length env)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (generatorAcquire logicalAnchors kind false target
        (comprehensionFilters filters (comprehensionTargetsBody [collectorTerminal logical.length element isSet dictionaryValue] rest))
        values logical globals (collectorEnter isSet dictionaryValue env stack))
      (generatorAcquire physicalAnchors kind false target
        (comprehensionFilters filters (comprehensionTargetsBody [collectorTerminal physical.length element isSet dictionaryValue] rest))
        (values.map (relocateValue rename)) physical (relocateGlobals rename globals)
        (collectorEnter isSet dictionaryValue (relocateEnv rename env) (stack.map (relocateFrame rename)))) := by
  apply collectorAcquireBody_preserves kind target
    (fun address => comprehensionFilters filters
      (comprehensionTargetsBody [collectorTerminal address element isSet dictionaryValue] rest))
    isSet dictionaryValue logical physical rename logicalAnchors physicalAnchors env values stack globals
    layout envInside valuesInside stackInside globalsInside
  · exact SetCalls.Relocation.comprehensionFilters_within _ filters _
      (SetCalls.Relocation.comprehensionTargetsBody_within _ _ rest (by
        intro statement member
        have same := List.mem_singleton.mp member
        subst statement
        exact collectorTerminal_within _ _ _ _ _ (Nat.lt_succ_self _)))
  · rw [← SetCalls.Relocation.comprehensionFilters_relocates,
      ← SetCalls.Relocation.comprehensionTargetsBody_relocates]
    simp only [List.map_cons, List.map_nil, collectorTerminal_relocates, extendMap_new]

theorem dictionaryValuesAllocated_preserves (target : Expr) (receiver : Value) (body : List Stmt)
    (isSet : Bool) (dictionaryValue : Option Expr) (logical physical : Mutable.Heap)
    (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat) (env : Env) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (receiverInside : receiver.edge.Within logical.length) (envInside : EnvWithin logical.length env)
    (bodyInside : ∀ statement ∈ body, StmtWithin (logical.length + 1) statement)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (dictionaryValuesStart logicalAnchors target body [] [] env receiver
        (.comprehensionResult logical.length :: stack) (logical ++ [collectorObject isSet dictionaryValue]) globals)
      (dictionaryValuesStart physicalAnchors target (body.map (relocateStmt (extendMap rename logical.length physical.length)))
        [] [] (relocateEnv rename env) (relocateValue rename receiver)
        (.comprehensionResult physical.length :: stack.map (relocateFrame rename))
        (physical ++ [collectorObject isSet dictionaryValue]) (relocateGlobals rename globals)) := by
  let nextMap := extendMap rename logical.length physical.length
  have agree : ∀ address < logical.length, nextMap address = rename address := extendMap_old _ _ _
  have larger : logical.length ≤ (logical ++ [collectorObject isSet dictionaryValue]).length := by simp
  have retained := layout.append_existing (collectorObject isSet dictionaryValue)
    (by cases dictionaryValue <;> cases isSet <;> simp [collectorObject])
    (by cases dictionaryValue <;> cases isSet <;> simp [collectorObject, ObjectWithin, objectValues])
  rw [collectorObject_relocates] at retained
  refine ⟨logical ++ [collectorObject isSet dictionaryValue], physical ++ [collectorObject isSet dictionaryValue],
    nextMap, agree, larger, by simp, retained, dictionaryValuesStart_heap .., ?_, ?_⟩
  · exact dictionary_start_within _ retained.closed logicalAnchors true target receiver body [] [] env
      (.comprehensionResult logical.length :: stack) globals
      (valueWithin_mono _ _ receiver larger receiverInside) (globalsInside.mono larger) (envInside.mono larger)
      (by
        intro frame member
        rcases List.mem_cons.mp member with rfl | member
        · simp [FrameWithin]
        · exact (stackInside frame member).mono larger)
      (by simpa using bodyInside) (by simp) (by simp)
  · have paired := dictionaryValuesStart_relocates _ _ nextMap retained.runtime logicalAnchors physicalAnchors
      target receiver body [] [] env (.comprehensionResult logical.length :: stack) globals
      (valueWithin_mono _ _ receiver larger receiverInside)
    simpa only [List.map_nil, List.map_cons, relocateFrame, nextMap, extendMap_new,
      relocateEnv_congr nextMap rename logical.length env agree envInside,
      relocateValue_congr nextMap rename logical.length receiver agree receiverInside,
      relocateStack_congr nextMap rename logical.length stack agree stackInside,
      relocateGlobals_congr nextMap rename logical.length globals agree globalsInside] using paired

end FormalSW.PyAst.HeapCalls.Relocation
