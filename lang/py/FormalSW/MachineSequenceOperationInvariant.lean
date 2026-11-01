import lang.py.FormalSW.MachineGeneratorContinuation
import lang.py.FormalSW.MachineLoopAcquisition

/-! Sequence operations acquire their cursors after retaining all argument effects. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_permutation_start_preserves (target : Expr) (values : List Value)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.permutationStart target body otherwise following env) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.permutationStart target body otherwise following env) values, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.permutationStart target body otherwise following env) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    apply run_readonly_heap
    · exact fun outcome after executed => permutationRows_keeps_heap logical values outcome after executed
    · intro _ _; rfl
  · exact StateWithin.permutation_start module logical layout.closed logicalAnchors target values
      body otherwise following env stack globals globalsInside inside
  · exact step_permutation_start_relocates module logical physical rename logicalAnchors physicalAnchors layout.runtime
      target values body otherwise following env stack globals inside.1.2

theorem step_combination_start_preserves (target : Expr) (values : List Value)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.combinationStart target body otherwise following env) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.combinationStart target body otherwise following env) values, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.combinationStart target body otherwise following env) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    apply run_readonly_heap
    · exact fun outcome after executed => combinationRows_keeps_heap logical values outcome after executed
    · intro _ _; rfl
  · exact StateWithin.combination_start module logical layout.closed logicalAnchors target values
      body otherwise following env stack globals globalsInside inside
  · exact step_combination_start_relocates module logical physical rename logicalAnchors physicalAnchors layout.runtime
      target values body otherwise following env stack globals inside.1.2

theorem step_zip_start_preserves (target : Expr) (values : List Value)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.zipStart target body otherwise following env) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.zipStart target body otherwise following env) values, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.zipStart target body otherwise following env) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    apply run_readonly_heap
    · exact fun outcome after executed => zipSources_keeps_heap logical values outcome after executed
    · intro _ _; rfl
  · exact StateWithin.zip_start module logical logicalAnchors target values
      body otherwise following env stack globals globalsInside inside
  · exact step_zip_start_relocates module logical physical rename logicalAnchors physicalAnchors layout.runtime
      target values body otherwise following env stack globals inside.1.2

/-- Validate the start value after sequence acquisition and preserve its shared identity. -/
theorem sumEnter_preserves (loop : Stmt) (env : Env) (value : Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (loopInside : StmtWithin logical.length loop) (envInside : EnvWithin logical.length env)
    (valueInside : value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (sumEnter logicalAnchors loop env value stack logical globals)
      (sumEnter physicalAnchors (relocateStmt rename loop) (relocateEnv rename env) (relocateValue rename value)
        (stack.map (relocateFrame rename)) physical (relocateGlobals rename globals)) := by
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ (relocateValue rename)
    _ _ globals layout globalsInside
    (fun outcome after executed => SetCalls.Relocation.sumInitial_keeps_heap logical after value outcome valueInside executed)
    (SetCalls.Relocation.sumInitial_relocates layout.runtime value valueInside)
  intro result executed
  have same := SetCalls.Relocation.sumInitial_value logical logical value result executed
  subst result
  apply Preserves.unchanged layout
  · rfl
  · exact ⟨⟨envInside.setLocal _ value valueInside, by simpa [StmtWithin] using loopInside⟩, stackInside⟩
  · simp only [relocateStep, relocateState, relocateWork, List.map_cons, List.map_nil,
      relocateStmt, relocateEnv_set]

theorem sumSequenceStart_preserves (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (sumSequenceStart logicalAnchors values stack logical globals)
      (sumSequenceStart physicalAnchors (values.map (relocateValue rename))
        (stack.map (relocateFrame rename)) physical (relocateGlobals rename globals)) := by
  rcases values with _ | ⟨source, _ | ⟨start, _ | ⟨extra, rest⟩⟩⟩
  all_goals first
    | exact Preserves.unchanged layout (by trivial) (by trivial) rfl
    | skip
  have sourceInside := valuesInside source (by simp)
  have startInside := valuesInside start (by simp)
  simp only [sumSequenceStart, List.map_cons, List.map_nil]
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _
    (List.map (relocateValue rename)) _ _ globals layout globalsInside
    (fun outcome after executed => sequence_keeps_heap logical after source outcome executed)
    (layout.runtime.sequence source sourceInside)
  intro items captured
  have bounded : StmtWithin logical.length
      (.sequenceStepLoop sumItem (sequenceSource source) 0 (sumBody (.name sumItem) []) []) := by
    simpa [sumBody, StmtWithin] using sequenceSource_within logical.length source sourceInside
  simpa only [relocateStmt, sequenceSource_relocate, sumBody, List.map_cons, List.map_nil,
    relocateEnv, Option.map_none] using
    sumEnter_preserves logical physical rename logicalAnchors physicalAnchors
      (.sequenceStepLoop sumItem (sequenceSource source) 0 (sumBody (.name sumItem) []) [])
      (fun _ => none) start stack globals layout bounded (by intro _ _ impossible; cases impossible)
      startInside stackInside globalsInside

theorem step_sumSequence_preserves (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation .sumSequence values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation .sumSequence values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation .sumSequence values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  exact (sumSequenceStart_preserves logical physical rename logicalAnchors physicalAnchors
    values stack globals layout inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2

theorem truthSequenceStart_preserves (universal : Bool) (values : List Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (truthSequenceStart logicalAnchors universal values stack logical globals)
      (truthSequenceStart physicalAnchors universal (values.map (relocateValue rename))
        (stack.map (relocateFrame rename)) physical (relocateGlobals rename globals)) := by
  rcases values with _ | ⟨source, _ | ⟨extra, rest⟩⟩
  case nil => exact Preserves.unchanged layout rfl ⟨globalsInside, by intro _ impossible; cases impossible⟩ rfl
  case cons.cons => exact Preserves.unchanged layout rfl ⟨globalsInside, by intro _ impossible; cases impossible⟩ rfl
  have sourceInside := valuesInside source (by simp)
  simp only [truthSequenceStart, List.map_cons, List.map_nil]
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _
    (List.map (relocateValue rename)) _ _ globals layout globalsInside
    (fun outcome after executed => sequence_keeps_heap logical after source outcome executed)
    (layout.runtime.sequence source sourceInside)
  intro items captured
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨⟨?_, ?_⟩, stackInside⟩
    · intro name value impossible
      cases impossible
    · have bounded := sequenceSource_within logical.length source sourceInside
      cases universal <;> simpa [truthBody, StmtWithin] using bounded
  · cases universal <;>
      simp [relocateStep, relocateState, relocateWork, relocateStmt, sequenceSource_relocate,
        truthBody]
    all_goals rfl

theorem step_truthSequence_preserves (universal : Bool) (values : List Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.builtin (if universal then .all else .any)) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.builtin (if universal then .all else .any)) values, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.builtin (if universal then .all else .any)) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have preserved := (truthSequenceStart_preserves logical physical rename logicalAnchors physicalAnchors
    universal values stack globals layout inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2
  cases universal <;> exact preserved

/-- Operations whose sequence acquisition is covered independently of subsequent loop execution. -/
inductive SequenceOperation : Operation → Prop
  | permutation (target body otherwise following env) :
      SequenceOperation (.permutationStart target body otherwise following env)
  | combination (target body otherwise following env) :
      SequenceOperation (.combinationStart target body otherwise following env)
  | zip (target body otherwise following env) : SequenceOperation (.zipStart target body otherwise following env)
  | sum : SequenceOperation .sumSequence
  | truth (universal : Bool) : SequenceOperation (.builtin (if universal then .all else .any))

theorem step_sequenceOperation_preserves (operation : Operation) (values : List Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (covered : SequenceOperation operation)
    (inside : StateWithin ⟨.operation operation values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation operation values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation operation values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases covered with
  | permutation => apply step_permutation_start_preserves <;> assumption
  | combination => apply step_combination_start_preserves <;> assumption
  | zip => apply step_zip_start_preserves <;> assumption
  | sum => apply step_sumSequence_preserves <;> assumption
  | truth => apply step_truthSequence_preserves <;> assumption

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_sequenceOperation_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (operation : Operation) (values : List Mutable.Value) (stack : List Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (covered : SequenceOperation operation)
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
    (HeapCalls.Relocation.step_sequenceOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      operation values stack globals layout covered ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
