import lang.py.FormalSW.MachineCollectorAllocation
import lang.py.FormalSW.MachineGeneratorConsumers

/-! Comprehension acquisition validates the input before allocating its result. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

def collectorBody (address : Nat) (element : Expr) (filters : List Expr)
    (rest : List (Expr × Expr × List Expr)) (isSet : Bool) (dictionaryValue : Option Expr) : List Stmt :=
  comprehensionFilters filters (comprehensionTargetsBody [collectorTerminal address element isSet dictionaryValue] rest)

theorem collectorBody_within (limit address : Nat) (element : Expr) (filters : List Expr)
    (rest : List (Expr × Expr × List Expr)) (isSet : Bool) (dictionaryValue : Option Expr) (inside : address < limit) :
    ∀ statement ∈ collectorBody address element filters rest isSet dictionaryValue, StmtWithin limit statement :=
  SetCalls.Relocation.comprehensionFilters_within _ _ _ (SetCalls.Relocation.comprehensionTargetsBody_within _ _ _
    (by simpa using collectorTerminal_within limit address element isSet dictionaryValue inside))

theorem collectorBody_relocates (rename : Nat → Nat) (address : Nat) (element : Expr) (filters : List Expr)
    (rest : List (Expr × Expr × List Expr)) (isSet : Bool) (dictionaryValue : Option Expr) :
    (collectorBody address element filters rest isSet dictionaryValue).map (relocateStmt rename) =
      collectorBody (rename address) element filters rest isSet dictionaryValue := by
  simp only [collectorBody, ← SetCalls.Relocation.comprehensionFilters_relocates,
    ← SetCalls.Relocation.comprehensionTargetsBody_relocates, List.map_cons, List.map_nil, collectorTerminal_relocates]

theorem dictionaryValuesCollectionStart_preserves (element target : Expr) (filters : List Expr)
    (rest : List (Expr × Expr × List Expr)) (isSet : Bool) (dictionaryValue : Option Expr)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (env : Env) (receiver : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (envInside : EnvWithin logical.length env)
    (receiverInside : receiver.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (dictionaryValuesCollectionStart logicalAnchors element target filters rest env receiver stack logical globals isSet dictionaryValue)
      (dictionaryValuesCollectionStart physicalAnchors element target filters rest (relocateEnv rename env)
        (relocateValue rename receiver) (stack.map (relocateFrame rename)) physical (relocateGlobals rename globals) isSet dictionaryValue) := by
  have allocated := dictionaryValuesAllocated_preserves target receiver
    (collectorBody logical.length element filters rest isSet dictionaryValue) isSet dictionaryValue
    logical physical rename logicalAnchors physicalAnchors env stack globals layout receiverInside envInside
    (collectorBody_within _ _ _ _ _ _ _ (Nat.lt_succ_self _)) stackInside globalsInside
  rw [collectorBody_relocates, extendMap_new] at allocated
  cases receiver with
  | scalar value =>
    exact Preserves.unchanged layout rfl ⟨globalsInside, by intro value impossible; cases impossible⟩ rfl
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem receiverInside
    have moved := layout.runtime.lookup address _ found
    cases object : logical[address] <;> simp only [object, relocateObject] at moved
    all_goals simp only [dictionaryValuesCollectionStart, relocateValue, found, object, moved, dictionaryItemFields]
    case dict entries => simpa only [collectorBody, collectorTerminal, collectorObject] using allocated
    case keyDict entries => simpa only [collectorBody, collectorTerminal, collectorObject] using allocated
    case «instance» origin className fields =>
      apply Preserves.unchanged layout
      · rfl
      · refine ⟨receiverInside, ?_⟩
        intro frame member
        rcases List.mem_cons.mp member with rfl | member
        · simp only [FrameWithin]
          exact envInside
        rcases List.mem_cons.mp member with rfl | member
        · cases dictionaryValue <;> cases isSet <;> simpa [FrameWithin, OperationWithin] using envInside
        · exact stackInside frame member
      · cases dictionaryValue <;> cases isSet <;>
          simp [relocateStep, relocateState, relocateWork, relocateFrame, relocateRuntimeOperation, relocateOperation, relocateValue]
    case dataInstance origin className frozen declared fields =>
      apply Preserves.unchanged layout
      · rfl
      · refine ⟨receiverInside, ?_⟩
        intro frame member
        rcases List.mem_cons.mp member with rfl | member
        · simp only [FrameWithin]
          exact envInside
        rcases List.mem_cons.mp member with rfl | member
        · cases dictionaryValue <;> cases isSet <;> simpa [FrameWithin, OperationWithin] using envInside
        · exact stackInside frame member
      · cases dictionaryValue <;> cases isSet <;>
          simp [relocateStep, relocateState, relocateWork, relocateFrame, relocateRuntimeOperation, relocateOperation, relocateValue]
    all_goals exact Preserves.unchanged layout rfl ⟨globalsInside, by intro value impossible; cases impossible⟩ rfl

theorem comprehensionTargetsStart_acquire (anchors : Nat) (element target iterable : Expr)
    (filters : List Expr) (rest : List (Expr × Expr × List Expr)) (env : Env)
    (values : List Value) (stack : List Frame) (heap : Mutable.Heap) (globals : Mutable.Globals)
    (isSet : Bool) (dictionaryValue : Option Expr) :
    comprehensionTargetsStart anchors element ((target, iterable, filters) :: rest) env values stack heap globals isSet dictionaryValue =
      match iterable with
      | .dictionaryValuesIterable _ => match values with
          | [value] => dictionaryValuesCollectionStart anchors element target filters rest env value stack heap globals isSet dictionaryValue
          | _ => .unsupported
      | _ => generatorAcquire anchors (generatorSource false iterable) false target
          (collectorBody heap.length element filters rest isSet dictionaryValue) values heap globals
          (collectorEnter isSet dictionaryValue env stack) := by
  cases iterable with
  | call function expressions =>
    cases function with
    | name name =>
      by_cases enumerateName : name = "enumerate"
      · subst name; rfl
      by_cases rangeName : name = "range"
      · subst name; rfl
      simp [comprehensionTargetsStart, generatorAcquire, generatorSource, generatorSequence,
        collectorBody, collectorTerminal, collectorEnter, collectorObject, enumerateName, rangeName]
      rfl
    | _ => rfl
  | _ => rfl

theorem comprehensionTargetsStart_preserves (element : Expr) (generators : List (Expr × Expr × List Expr))
    (isSet : Bool) (dictionaryValue : Option Expr) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (env : Env) (values : List Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (envInside : EnvWithin logical.length env)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (comprehensionTargetsStart logicalAnchors element generators env values stack logical globals isSet dictionaryValue)
      (comprehensionTargetsStart physicalAnchors element generators (relocateEnv rename env)
        (values.map (relocateValue rename)) (stack.map (relocateFrame rename)) physical
        (relocateGlobals rename globals) isSet dictionaryValue) := by
  cases generators with
  | nil => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  | cons generator rest =>
    rcases generator with ⟨target, iterable, filters⟩
    rw [comprehensionTargetsStart_acquire, comprehensionTargetsStart_acquire]
    cases iterable with
    | dictionaryValuesIterable expression =>
      rcases values with _ | ⟨value, _ | ⟨extra, tail⟩⟩
      case nil => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
      case cons.cons => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
      exact dictionaryValuesCollectionStart_preserves element target filters rest isSet dictionaryValue
        logical physical rename logicalAnchors physicalAnchors env value stack globals layout envInside
        (valuesInside value (by simp)) stackInside globalsInside
    | _ => apply collectorAcquire_preserves <;> assumption

theorem comprehensionStart_acquire (anchors : Nat) (element : Expr) (name : String) (iterable : Expr)
    (filters : List Expr) (rest : List (String × Expr × List Expr)) (env : Env)
    (values : List Value) (stack : List Frame) (heap : Mutable.Heap) (globals : Mutable.Globals) :
    comprehensionStart anchors element ((name, iterable, filters) :: rest) env values stack heap globals =
      generatorAcquire anchors (simpleGeneratorSource iterable) false (.name name)
        (comprehensionFilters filters (comprehensionBody heap.length element rest)) values heap globals
        (collectorEnter false none env stack) := by
  cases iterable with
  | call function expressions =>
    cases function with
    | name functionName =>
      by_cases rangeName : functionName = "range"
      · subst functionName; rfl
      simp [comprehensionStart, generatorAcquire, simpleGeneratorSource, generatorSequence, rangeName,
        comprehensionTargetName, comprehensionTargetBody, collectorEnter, collectorObject]
      rfl
    | _ => rfl
  | _ => rfl

theorem comprehensionStart_preserves (element : Expr) (generators : List (String × Expr × List Expr))
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (env : Env) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (envInside : EnvWithin logical.length env)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (comprehensionStart logicalAnchors element generators env values stack logical globals)
      (comprehensionStart physicalAnchors element generators (relocateEnv rename env)
        (values.map (relocateValue rename)) (stack.map (relocateFrame rename)) physical (relocateGlobals rename globals)) := by
  cases generators with
  | nil => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  | cons generator rest =>
    rcases generator with ⟨name, iterable, filters⟩
    rw [comprehensionStart_acquire, comprehensionStart_acquire]
    apply collectorAcquireBody_preserves (simpleGeneratorSource iterable) (.name name)
      (fun address => comprehensionFilters filters (comprehensionBody address element rest)) false none
      logical physical rename logicalAnchors physicalAnchors env values stack globals
      layout envInside valuesInside stackInside globalsInside
    · exact SetCalls.Relocation.comprehensionFilters_within _ filters _
        (SetCalls.Relocation.comprehensionBody_within _ _ element rest (Nat.lt_succ_self _))
    · rw [← SetCalls.Relocation.comprehensionFilters_relocates,
        ← SetCalls.Relocation.comprehensionBody_relocates, extendMap_new]

inductive CollectorOperation : Operation → Prop
  | listSimple (element generators env) : CollectorOperation (.comprehension element generators env)
  | list (element generators env) : CollectorOperation (.comprehensionTargets element generators env)
  | set (element generators env) : CollectorOperation (.setComprehension element generators env)
  | dictionary (key value generators env) : CollectorOperation (.dictionaryComprehension key value generators env)
  | generator (action element generators env) : CollectorOperation (.generatorCollect action element generators env)

theorem step_collectorOperation_preserves (module : Module)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (operation : Operation) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (covered : CollectorOperation operation)
    (inside : StateWithin ⟨.operation operation values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation operation values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation operation values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases covered with
  | listSimple element generators env =>
    exact (comprehensionStart_preserves element generators logical physical rename logicalAnchors physicalAnchors
      env values stack globals layout inside.1.1 inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2
  | list element generators env =>
    exact (comprehensionTargetsStart_preserves element generators false none logical physical rename logicalAnchors physicalAnchors
      env values stack globals layout inside.1.1 inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2
  | set element generators env =>
    exact (comprehensionTargetsStart_preserves element generators true none logical physical rename logicalAnchors physicalAnchors
      env values stack globals layout inside.1.1 inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2
  | dictionary key value generators env =>
    exact (comprehensionTargetsStart_preserves key generators false (some value) logical physical rename logicalAnchors physicalAnchors
      env values stack globals layout inside.1.1 inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2
  | generator action element generators env =>
    have stackInside : ∀ frame ∈ .generatorEnd :: .generatorConsumer action :: stack, FrameWithin logical.length frame := by
      intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · simp only [FrameWithin]
      rcases List.mem_cons.mp member with rfl | member
      · simp only [FrameWithin]
      · exact inside.2 frame member
    have preserved := (comprehensionTargetsStart_preserves element generators false none logical physical rename logicalAnchors physicalAnchors
      env values (.generatorEnd :: .generatorConsumer action :: stack) globals layout inside.1.1 inside.1.2 stackInside globalsInside)
    simpa only [step, relocateState, relocateWork, relocateRuntimeOperation, relocateOperation, List.map_cons, relocateFrame] using
      preserved.protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_collectorOperation_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (operation : Operation) (values : List Mutable.Value) (stack : List Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (covered : CollectorOperation operation)
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
    (HeapCalls.Relocation.step_collectorOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      operation values stack globals layout covered ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
