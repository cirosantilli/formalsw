import lang.py.FormalSW.MachineGeneratorEntry
import lang.py.FormalSW.MachineRunInvariant

/-! Generator continuations retain captured values and suspended exception boundaries. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_nextStart_preserves (value : Value) (hasDefault : Bool) (loop : Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .nextStart hasDefault loop env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .nextStart hasDefault loop env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .nextStart hasDefault loop env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have captured := inside.2 (.nextStart hasDefault loop env) (by simp)
  simp only [FrameWithin] at captured
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact captured.1.setLocal _ value inside.1
    · simp only [List.singleton_append, List.mem_cons, forall_eq_or_imp]
      exact ⟨captured.2, by cases hasDefault <;> simp [nextFinish, StmtWithin]⟩
    · intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · simp only [FrameWithin]
      · exact inside.2 frame (List.mem_cons_of_mem _ member)
  · cases hasDefault <;>
      simp [step, relocateState, relocateWork, relocateFrame, relocateStep,
        nextEnv, nextFinish, relocateEnv_set, relocateStmt, relocateValue]

theorem step_extremumStart_preserves (value : Value) (hasDefault : Bool) (loop : Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .extremumStart hasDefault loop env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .extremumStart hasDefault loop env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .extremumStart hasDefault loop env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have captured := inside.2 (.extremumStart hasDefault loop env) (by simp)
  simp only [FrameWithin] at captured
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (captured.1.setLocal _ (.scalar (.bool false)) (by trivial)).setLocal _ value inside.1
    · simp only [List.singleton_append, List.mem_cons, forall_eq_or_imp]
      exact ⟨captured.2, by cases hasDefault <;> simp [extremumFinish, StmtWithin]⟩
    · intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · simp only [FrameWithin]
      · exact inside.2 frame (List.mem_cons_of_mem _ member)
  · cases hasDefault <;>
      simp [step, relocateState, relocateWork, relocateFrame, relocateStep,
        extremumEnv, extremumFinish, relocateEnv_set, relocateStmt, relocateValue]

theorem step_extremumResume_preserves (value : Value) (original stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .extremumResume original :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .extremumResume original :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .extremumResume original :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · rfl
  · exact ⟨inside.1, by simpa only [FrameWithin] using inside.2 (.extremumResume original) (List.mem_cons_self ..)⟩
  · simp [step, relocateState, relocateWork, relocateFrame, relocateStep]

theorem step_generatorEnd_preserves (value : Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .generatorEnd :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .generatorEnd :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .generatorEnd :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · rfl
  · exact ⟨inside.1, fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)⟩
  · simp [step, relocateState, relocateWork, relocateFrame, relocateStep]

theorem step_generatorConsumer_preserves (value : Value) (action : GeneratorAction) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .generatorConsumer action :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .generatorConsumer action :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .generatorConsumer action :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame :=
    fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)
  cases action
  all_goals
    apply Preserves.unchanged layout
    · rfl
    · first
      | exact ⟨inside.1, stackInside⟩
      | exact ⟨⟨by trivial, by simpa [Mutable.Value.edge, Graph.Edge.Within] using inside.1⟩, stackInside⟩
    · simp [step, relocateState, relocateWork, relocateFrame, relocateStep,
        relocateRuntimeOperation, relocateOperation, relocateValue]

theorem step_sumStart_preserves (value : Value) (loop : Stmt) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .sumStart loop env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .sumStart loop env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .sumStart loop env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have captured := inside.2 (.sumStart loop env) (by simp)
  simp only [FrameWithin] at captured
  have raw := run_readonly_preserves logical physical rename logicalAnchors physicalAnchors
    (sumInitial value) (sumInitial (relocateValue rename value)) (relocateValue rename)
    (fun result heap => .next ⟨.block [loop, .return (.name sumAccumulator)]
      (setLocal env sumAccumulator result), .generatorEnd :: stack, heap⟩)
    (fun result heap => .next ⟨.block [relocateStmt rename loop, .return (.name sumAccumulator)]
      (setLocal (relocateEnv rename env) sumAccumulator result), .generatorEnd :: stack.map (relocateFrame rename), heap⟩)
    globals layout globalsInside
    (fun outcome after executed => SetCalls.Relocation.sumInitial_keeps_heap logical after value outcome inside.1 executed)
    (SetCalls.Relocation.sumInitial_relocates layout.runtime value inside.1) (by
      intro result executed
      have same := SetCalls.Relocation.sumInitial_value logical logical value result executed
      subst result
      apply Preserves.unchanged layout
      · rfl
      · refine ⟨⟨captured.1.setLocal _ value inside.1, ?_⟩, ?_⟩
        · simpa [StmtWithin] using captured.2
        · intro frame member
          rcases List.mem_cons.mp member with rfl | member
          · simp only [FrameWithin]
          · exact inside.2 frame (List.mem_cons_of_mem _ member)
      · simp only [relocateStep, relocateState, relocateWork, List.map_cons, List.map_nil,
          relocateStmt, relocateFrame, relocateEnv_set])
  simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame, sumEnter] using
    raw.protectGenerator (.sumStart loop env :: stack) inside.2

theorem step_generatorReceiver_preserves (value : Value) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) (env : Env) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .generatorReceiver element generators env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .generatorReceiver element generators env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .generatorReceiver element generators env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have envInside := inside.2 (.generatorReceiver element generators env) (by simp)
  simp only [FrameWithin] at envInside
  have stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame :=
    fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)
  have raw := run_readonly_preserves logical physical rename logicalAnchors physicalAnchors
    (bindMethod module value "join") (bindMethod module (relocateValue rename value) "join") (relocateOperation rename)
    (fun selected heap => match selected with
      | .join separator => .next (generatorArguments (.join separator) element generators env stack heap)
      | _ => .unsupported)
    (fun selected heap => match selected with
      | .join separator => .next (generatorArguments (.join separator) element generators
          (relocateEnv rename env) (stack.map (relocateFrame rename)) heap)
      | _ => .unsupported)
    globals layout globalsInside
    (fun outcome after executed => bindMethod_keeps_heap module value "join" logical after outcome inside.1 executed)
    (bindMethod_relocates logical physical rename layout.runtime module value "join" inside.1) (by
      intro selected _
      cases selected
      all_goals first
        | exact generator_arguments_preserves logical physical rename physicalAnchors env stack layout envInside stackInside _ element generators
        | exact Preserves.unchanged layout trivial trivial rfl)
  simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame] using
    raw.protectGenerator (.generatorReceiver element generators env :: stack) inside.2

/-- The continuation frames introduced by generator entry and its consumers. -/
inductive GeneratorContinuation : Frame → Prop where
  | next (hasDefault : Bool) (loop : Stmt) (env : Env) : GeneratorContinuation (.nextStart hasDefault loop env)
  | extremum (hasDefault : Bool) (loop : Stmt) (env : Env) : GeneratorContinuation (.extremumStart hasDefault loop env)
  | resume (original : List Frame) : GeneratorContinuation (.extremumResume original)
  | boundary : GeneratorContinuation .generatorEnd
  | consumer (action : GeneratorAction) : GeneratorContinuation (.generatorConsumer action)
  | sum (loop : Stmt) (env : Env) : GeneratorContinuation (.sumStart loop env)
  | receiver (element : Expr) (generators : List (Expr × Expr × List Expr)) (env : Env) :
      GeneratorContinuation (.generatorReceiver element generators env)

theorem step_generatorContinuation_preserves (value : Value) (frame : Frame) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (generator : GeneratorContinuation frame)
    (inside : StateWithin ⟨.value value, frame :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, frame :: stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value value, frame :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases generator with
  | next => apply step_nextStart_preserves <;> assumption
  | extremum => apply step_extremumStart_preserves <;> assumption
  | resume => apply step_extremumResume_preserves <;> assumption
  | boundary => apply step_generatorEnd_preserves <;> assumption
  | consumer => apply step_generatorConsumer_preserves <;> assumption
  | sum => apply step_sumStart_preserves <;> assumption
  | receiver => apply step_generatorReceiver_preserves <;> assumption

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_generatorContinuation_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (value : Mutable.Value) (frame : HeapCalls.Frame) (stack : List HeapCalls.Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module)
    (layout : ExecutionLayout logical physical rename) (generator : GeneratorContinuation frame)
    (inside : StateWithin logical.length (.running ⟨⟨.value value, frame :: stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running ⟨⟨.value value, frame :: stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running ⟨⟨.value value, frame :: stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running ⟨⟨.value value, frame :: stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_generatorContinuation_preserves module logical physical rename logicalAnchors physicalAnchors
      value frame stack globals layout generator ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
