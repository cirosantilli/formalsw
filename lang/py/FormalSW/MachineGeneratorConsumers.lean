import lang.py.FormalSW.MachineDictionaryItemsSum

/-! Generator consumers acquire the first iterator before defaults and retain lazy bodies. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem nextGeneratorStart_acquire (anchors : Nat) (fallback : Option Expr) (element target iterable : Expr)
    (filters : List Expr) (rest : List (Expr × Expr × List Expr)) (env : Env)
    (values : List Value) (stack : List Frame) (heap : Mutable.Heap) (globals : Mutable.Globals) :
    nextGeneratorStart anchors fallback element ((target, iterable, filters) :: rest) env values stack heap globals =
      generatorAcquire anchors (generatorSource true iterable) true target
        (comprehensionFilters filters (comprehensionTargetsBody ([.return element]) rest)) values heap globals
        (fun loop heap => .next ⟨.expr (fallback.getD (.constant .none)) env,
        .nextStart fallback.isSome loop (comprehensionTargetsEnv env ((target, iterable, filters) :: rest)) :: stack, heap⟩) := by
  cases iterable with
  | call function expressions =>
    cases function with
    | name name =>
      by_cases enumerateName : name = "enumerate"
      · subst name; rfl
      by_cases rangeName : name = "range"
      · subst name; rfl
      simp [nextGeneratorStart, generatorAcquire, generatorSource, generatorSequence, enumerateName, rangeName]
      rfl
    | _ => rfl
  | _ => rfl

theorem extremumGeneratorStart_acquire (anchors : Nat) (maximum : Bool) (fallback : Option Expr) (element target iterable : Expr)
    (filters : List Expr) (rest : List (Expr × Expr × List Expr)) (env : Env)
    (values : List Value) (stack : List Frame) (heap : Mutable.Heap) (globals : Mutable.Globals) :
    extremumGeneratorStart anchors maximum fallback element ((target, iterable, filters) :: rest) env values stack heap globals =
      generatorAcquire anchors (generatorSource false iterable) false target
        (comprehensionFilters filters (comprehensionTargetsBody (extremumBody maximum element) rest)) values heap globals
        (fun loop heap => .next ⟨.expr (fallback.getD (.constant .none)) env,
        .extremumStart fallback.isSome loop (comprehensionTargetsEnv env ((target, iterable, filters) :: rest)) :: stack, heap⟩) := by
  cases iterable with
  | call function expressions =>
    cases function with
    | name name =>
      by_cases enumerateName : name = "enumerate"
      · subst name; rfl
      by_cases rangeName : name = "range"
      · subst name; rfl
      simp [extremumGeneratorStart, generatorAcquire, generatorSource, generatorSequence, enumerateName, rangeName]
      rfl
    | _ => rfl
  | _ => rfl

theorem sumGeneratorTargetsStart_acquire (anchors : Nat) (start : Expr) (element target iterable : Expr)
    (filters : List Expr) (rest : List (Expr × Expr × List Expr)) (env : Env)
    (values : List Value) (stack : List Frame) (heap : Mutable.Heap) (globals : Mutable.Globals)
    (ordinary : itemsReceiver iterable = none) :
    sumGeneratorTargetsStart anchors element ((target, iterable, filters) :: rest) env start values stack heap globals =
      generatorAcquire anchors (generatorSource false iterable) false target
        (comprehensionFilters filters (comprehensionTargetsBody (sumBody element []) rest)) values heap globals
        (fun loop heap => .next ⟨.expr start env,
        .sumStart loop (comprehensionTargetsEnv env ((target, iterable, filters) :: rest)) :: stack, heap⟩) := by
  simp only [sumGeneratorTargetsStart, ordinary]
  cases iterable with
  | call function expressions =>
    cases function with
    | name name =>
      by_cases enumerateName : name = "enumerate"
      · subst name; rfl
      by_cases rangeName : name = "range"
      · subst name; rfl
      simp [generatorAcquire, generatorSource, generatorSequence, enumerateName, rangeName]
      rfl
    | _ => rfl
  | _ => rfl

theorem truthGeneratorStart_acquire (anchors : Nat) (universal : Bool) (element target iterable : Expr)
    (filters : List Expr) (rest : List (Expr × Expr × List Expr)) (env : Env)
    (values : List Value) (stack : List Frame) (heap : Mutable.Heap) (globals : Mutable.Globals) :
    truthGeneratorStart anchors universal element ((target, iterable, filters) :: rest) env values stack heap globals =
      generatorAcquire anchors (generatorSource false iterable) false target
        (comprehensionFilters filters (comprehensionTargetsBody (truthBody universal element) rest)) values heap globals
        (fun loop heap => .next ⟨.block [loop, .return (.constant (.bool universal))] env, .generatorEnd :: stack, heap⟩) := by
  cases iterable with
  | call function expressions =>
    cases function with
    | name name =>
      by_cases enumerateName : name = "enumerate"
      · subst name; rfl
      by_cases rangeName : name = "range"
      · subst name; rfl
      simp [truthGeneratorStart, generatorAcquire, generatorSource, generatorSequence, enumerateName, rangeName]
      rfl
    | _ => rfl
  | _ => rfl

theorem nextGeneratorStart_preserves (fallback : Option Expr) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) (env : Env)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (envInside : EnvWithin logical.length env)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (nextGeneratorStart logicalAnchors fallback element generators env values stack logical globals)
      (nextGeneratorStart physicalAnchors fallback element generators (relocateEnv rename env)
        (values.map (relocateValue rename)) (stack.map (relocateFrame rename)) physical (relocateGlobals rename globals)) := by
  cases generators with
  | nil => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  | cons generator rest =>
    rcases generator with ⟨target, iterable, filters⟩
    let body := comprehensionFilters filters (comprehensionTargetsBody ([.return element]) rest)
    have bodySource : ∀ statement ∈ body, StmtWithin 0 statement :=
      SetCalls.Relocation.comprehensionFilters_within 0 filters _
        (SetCalls.Relocation.comprehensionTargetsBody_within 0 ([.return element]) rest (by simp [StmtWithin]))
    have preserved := generatorAcquire_preserves (generatorSource true iterable) true target
      logical physical rename logicalAnchors physicalAnchors body values globals
      (fun loop heap => .next ⟨.expr (fallback.getD (.constant .none)) env, .nextStart fallback.isSome loop
          (comprehensionTargetsEnv env ((target, iterable, filters) :: rest)) :: stack, heap⟩)
      (fun loop heap => .next ⟨.expr (fallback.getD (.constant .none)) (relocateEnv rename env), .nextStart fallback.isSome loop
          (comprehensionTargetsEnv (relocateEnv rename env) ((target, iterable, filters) :: rest)) :: (stack.map (relocateFrame rename)), heap⟩)
      layout (fun statement member => (bodySource statement member).mono (Nat.zero_le _)) valuesInside globalsInside (by
      intro loop loopInside
      apply Preserves.unchanged layout
      · rfl
      · refine ⟨envInside, ?_⟩
        intro frame member
        rcases List.mem_cons.mp member with rfl | member
        · simp only [FrameWithin]
          exact ⟨SetCalls.Relocation.comprehensionTargetsEnv_within logical.length env _ envInside, loopInside⟩
        · exact stackInside frame member
      · simp only [relocateStep, relocateState, relocateWork, List.map_cons,
          relocateFrame, SetCalls.Relocation.comprehensionTargetsEnv_relocates])
    simpa only [nextGeneratorStart_acquire, relocateBody_source rename body bodySource] using preserved

theorem extremumGeneratorStart_preserves (maximum : Bool) (fallback : Option Expr) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) (env : Env)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (envInside : EnvWithin logical.length env)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (extremumGeneratorStart logicalAnchors maximum fallback element generators env values stack logical globals)
      (extremumGeneratorStart physicalAnchors maximum fallback element generators (relocateEnv rename env)
        (values.map (relocateValue rename)) (stack.map (relocateFrame rename)) physical (relocateGlobals rename globals)) := by
  cases generators with
  | nil => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  | cons generator rest =>
    rcases generator with ⟨target, iterable, filters⟩
    let body := comprehensionFilters filters (comprehensionTargetsBody (extremumBody maximum element) rest)
    have bodySource : ∀ statement ∈ body, StmtWithin 0 statement :=
      SetCalls.Relocation.comprehensionFilters_within 0 filters _
        (SetCalls.Relocation.comprehensionTargetsBody_within 0 (extremumBody maximum element) rest (by simp [extremumBody, StmtWithin]))
    have preserved := generatorAcquire_preserves (generatorSource false iterable) false target
      logical physical rename logicalAnchors physicalAnchors body values globals
      (fun loop heap => .next ⟨.expr (fallback.getD (.constant .none)) env, .extremumStart fallback.isSome loop
          (comprehensionTargetsEnv env ((target, iterable, filters) :: rest)) :: stack, heap⟩)
      (fun loop heap => .next ⟨.expr (fallback.getD (.constant .none)) (relocateEnv rename env), .extremumStart fallback.isSome loop
          (comprehensionTargetsEnv (relocateEnv rename env) ((target, iterable, filters) :: rest)) :: (stack.map (relocateFrame rename)), heap⟩)
      layout (fun statement member => (bodySource statement member).mono (Nat.zero_le _)) valuesInside globalsInside (by
      intro loop loopInside
      apply Preserves.unchanged layout
      · rfl
      · refine ⟨envInside, ?_⟩
        intro frame member
        rcases List.mem_cons.mp member with rfl | member
        · simp only [FrameWithin]
          exact ⟨SetCalls.Relocation.comprehensionTargetsEnv_within logical.length env _ envInside, loopInside⟩
        · exact stackInside frame member
      · simp only [relocateStep, relocateState, relocateWork, List.map_cons,
          relocateFrame, SetCalls.Relocation.comprehensionTargetsEnv_relocates])
    simpa only [extremumGeneratorStart_acquire, relocateBody_source rename body bodySource] using preserved

theorem sumGeneratorTargetsStart_preserves (start : Expr) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) (env : Env)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (envInside : EnvWithin logical.length env)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (sumGeneratorTargetsStart logicalAnchors element generators env start values stack logical globals)
      (sumGeneratorTargetsStart physicalAnchors element generators (relocateEnv rename env) start
        (values.map (relocateValue rename)) (stack.map (relocateFrame rename)) physical (relocateGlobals rename globals)) := by
  cases generators with
  | nil => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  | cons generator rest =>
    rcases generator with ⟨target, iterable, filters⟩
    cases ordinary : itemsReceiver iterable with
    | some receiver =>
      simpa only [sumGeneratorTargetsStart, ordinary] using
        dictionaryItemsSumStart_preserves element target iterable filters rest start
          logical physical rename logicalAnchors physicalAnchors env values stack globals
          layout envInside valuesInside stackInside globalsInside
    | none =>
      let body := comprehensionFilters filters (comprehensionTargetsBody (sumBody element []) rest)
      have bodySource : ∀ statement ∈ body, StmtWithin 0 statement :=
        SetCalls.Relocation.comprehensionFilters_within 0 filters _
          (SetCalls.Relocation.comprehensionTargetsBody_within 0 (sumBody element []) rest (SetCalls.Relocation.sumBody_source element []))
      have preserved := generatorAcquire_preserves (generatorSource false iterable) false target
        logical physical rename logicalAnchors physicalAnchors body values globals
        (fun loop heap => .next ⟨.expr start env, .sumStart loop
            (comprehensionTargetsEnv env ((target, iterable, filters) :: rest)) :: stack, heap⟩)
        (fun loop heap => .next ⟨.expr start (relocateEnv rename env), .sumStart loop
            (comprehensionTargetsEnv (relocateEnv rename env) ((target, iterable, filters) :: rest)) :: (stack.map (relocateFrame rename)), heap⟩)
        layout (fun statement member => (bodySource statement member).mono (Nat.zero_le _)) valuesInside globalsInside (by
        intro loop loopInside
        apply Preserves.unchanged layout
        · rfl
        · refine ⟨envInside, ?_⟩
          intro frame member
          rcases List.mem_cons.mp member with rfl | member
          · simp only [FrameWithin]
            exact ⟨SetCalls.Relocation.comprehensionTargetsEnv_within logical.length env _ envInside, loopInside⟩
          · exact stackInside frame member
        · simp only [relocateStep, relocateState, relocateWork, List.map_cons,
            relocateFrame, SetCalls.Relocation.comprehensionTargetsEnv_relocates])
      simpa only [sumGeneratorTargetsStart_acquire (ordinary := ordinary), relocateBody_source rename body bodySource] using preserved

theorem truthGeneratorStart_preserves (universal : Bool) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) (env : Env)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (envInside : EnvWithin logical.length env)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (truthGeneratorStart logicalAnchors universal element generators env values stack logical globals)
      (truthGeneratorStart physicalAnchors universal element generators (relocateEnv rename env)
        (values.map (relocateValue rename)) (stack.map (relocateFrame rename)) physical (relocateGlobals rename globals)) := by
  cases generators with
  | nil => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  | cons generator rest =>
    rcases generator with ⟨target, iterable, filters⟩
    let body := comprehensionFilters filters (comprehensionTargetsBody (truthBody universal element) rest)
    have bodySource : ∀ statement ∈ body, StmtWithin 0 statement :=
      SetCalls.Relocation.comprehensionFilters_within 0 filters _
        (SetCalls.Relocation.comprehensionTargetsBody_within 0 (truthBody universal element) rest (by cases universal <;> simp [truthBody, StmtWithin]))
    have preserved := generatorAcquire_preserves (generatorSource false iterable) false target
      logical physical rename logicalAnchors physicalAnchors body values globals
      (fun loop heap => .next ⟨.block [loop, .return (.constant (.bool universal))] env, .generatorEnd :: stack, heap⟩)
      (fun loop heap => .next ⟨.block [loop, .return (.constant (.bool universal))] (relocateEnv rename env), .generatorEnd :: (stack.map (relocateFrame rename)), heap⟩)
      layout (fun statement member => (bodySource statement member).mono (Nat.zero_le _)) valuesInside globalsInside (by
      intro loop loopInside
      apply Preserves.unchanged layout
      · rfl
      · refine ⟨⟨envInside, ?_⟩, ?_⟩
        · simpa [StmtWithin] using loopInside
        · intro frame member
          rcases List.mem_cons.mp member with rfl | member
          · simp only [FrameWithin]
          · exact stackInside frame member
      · simp only [relocateStep, relocateState, relocateWork, List.map_cons, List.map_nil,
          relocateStmt, relocateFrame])
    simpa only [truthGeneratorStart_acquire, relocateBody_source rename body bodySource] using preserved

/-- The legacy single-name sum syntax recognizes range and ordinary sequences. -/
def simpleGeneratorSource : Expr → GeneratorSource
  | .call (.name "range") _ => .range
  | _ => .sequence

theorem sumGeneratorStart_acquire (anchors : Nat) (element : Expr) (name : String) (iterable : Expr)
    (filters : List Expr) (rest : List (String × Expr × List Expr)) (env : Env) (start : Expr)
    (values : List Value) (stack : List Frame) (heap : Mutable.Heap) (globals : Mutable.Globals) :
    sumGeneratorStart anchors element ((name, iterable, filters) :: rest) env start values stack heap globals =
      generatorAcquire anchors (simpleGeneratorSource iterable) false (.name name)
        (comprehensionFilters filters (sumBody element rest)) values heap globals
        (fun loop heap => .next ⟨.expr start env,
          .sumStart loop (comprehensionEnv env ((name, iterable, filters) :: rest)) :: stack, heap⟩) := by
  cases iterable with
  | call function expressions =>
    cases function with
    | name functionName =>
      by_cases rangeName : functionName = "range"
      · subst functionName; rfl
      simp [sumGeneratorStart, generatorAcquire, simpleGeneratorSource, generatorSequence, rangeName,
        comprehensionTargetName, comprehensionTargetBody]
      rfl
    | _ => rfl
  | _ => rfl

theorem sumGeneratorStart_preserves (element : Expr) (generators : List (String × Expr × List Expr))
    (env : Env) (start : Expr) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (envInside : EnvWithin logical.length env)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (sumGeneratorStart logicalAnchors element generators env start values stack logical globals)
      (sumGeneratorStart physicalAnchors element generators (relocateEnv rename env) start
        (values.map (relocateValue rename)) (stack.map (relocateFrame rename)) physical (relocateGlobals rename globals)) := by
  cases generators with
  | nil => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  | cons generator rest =>
    rcases generator with ⟨name, iterable, filters⟩
    let body := comprehensionFilters filters (sumBody element rest)
    have bodySource : ∀ statement ∈ body, StmtWithin 0 statement :=
      SetCalls.Relocation.comprehensionFilters_within 0 filters _ (SetCalls.Relocation.sumBody_source element rest)
    have preserved := generatorAcquire_preserves (simpleGeneratorSource iterable) false (.name name)
      logical physical rename logicalAnchors physicalAnchors body values globals
      (fun loop heap => .next ⟨.expr start env,
        .sumStart loop (comprehensionEnv env ((name, iterable, filters) :: rest)) :: stack, heap⟩)
      (fun loop heap => .next ⟨.expr start (relocateEnv rename env),
        .sumStart loop (comprehensionEnv (relocateEnv rename env) ((name, iterable, filters) :: rest)) ::
          stack.map (relocateFrame rename), heap⟩)
      layout (fun statement member => (bodySource statement member).mono (Nat.zero_le _)) valuesInside globalsInside (by
      intro loop loopInside
      apply Preserves.unchanged layout
      · rfl
      · refine ⟨envInside, ?_⟩
        intro frame member
        rcases List.mem_cons.mp member with rfl | member
        · simp only [FrameWithin]
          exact ⟨SetCalls.Relocation.comprehensionEnv_within logical.length env _ envInside, loopInside⟩
        · exact stackInside frame member
      · simp only [relocateStep, relocateState, relocateWork, List.map_cons,
          relocateFrame, SetCalls.Relocation.comprehensionEnv_relocates])
    simpa only [sumGeneratorStart_acquire, relocateBody_source rename body bodySource] using preserved

inductive GeneratorConsumerOperation : Operation → Prop
  | next (fallback element generators env) : GeneratorConsumerOperation (.nextGenerator fallback element generators env)
  | extremum (maximum fallback element generators env) :
      GeneratorConsumerOperation (.extremumGenerator maximum fallback element generators env)
  | sumSimple (element generators env start) : GeneratorConsumerOperation (.sumGenerator element generators env start)
  | sum (element generators env start) : GeneratorConsumerOperation (.sumGeneratorTargets element generators env start)
  | truth (universal element generators env) : GeneratorConsumerOperation (.truthGenerator universal element generators env)

theorem step_generatorConsumerOperation_preserves (module : Module)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (operation : Operation) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (covered : GeneratorConsumerOperation operation)
    (inside : StateWithin ⟨.operation operation values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation operation values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation operation values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases covered with
  | next fallback element generators env =>
    exact (nextGeneratorStart_preserves fallback element generators env logical physical rename logicalAnchors physicalAnchors
      values stack globals layout inside.1.1 inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2
  | extremum maximum fallback element generators env =>
    exact (extremumGeneratorStart_preserves maximum fallback element generators env logical physical rename logicalAnchors physicalAnchors
      values stack globals layout inside.1.1 inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2
  | sumSimple element generators env start =>
    exact (sumGeneratorStart_preserves element generators env start logical physical rename logicalAnchors physicalAnchors
      values stack globals layout inside.1.1 inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2
  | sum element generators env start =>
    exact (sumGeneratorTargetsStart_preserves start element generators env logical physical rename logicalAnchors physicalAnchors
      values stack globals layout inside.1.1 inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2
  | truth universal element generators env =>
    exact (truthGeneratorStart_preserves universal element generators env logical physical rename logicalAnchors physicalAnchors
      values stack globals layout inside.1.1 inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_generatorConsumerOperation_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (operation : Operation) (values : List Mutable.Value) (stack : List Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (covered : GeneratorConsumerOperation operation)
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
    (HeapCalls.Relocation.step_generatorConsumerOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      operation values stack globals layout covered ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
