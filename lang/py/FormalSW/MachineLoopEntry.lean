import lang.py.FormalSW.MachineLoops

/-! Loop entry evaluates arguments before conversion and retains the original sequence object. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem rangeBounds_relocate (rename : Nat → Nat) (values : List Value) :
    rangeBounds (values.map (relocateValue rename)) = rangeBounds values := by
  have scalars :
      (values.map (relocateValue rename)).mapM (fun value => match value with
        | .scalar scalar => Except.ok scalar
        | .ref _ => Except.error ({ typeName := "TypeError", args := [] } : ExceptionObject)) =
      values.mapM (fun value => match value with
        | .scalar scalar => Except.ok scalar
        | .ref _ => Except.error ({ typeName := "TypeError", args := [] } : ExceptionObject)) := by
    induction values with
    | nil => rfl
    | cons value rest ih => cases value <;> simp [relocateValue, List.mapM_cons, ih]
  exact congrArg (fun converted : Except ExceptionObject (List Constant) => converted.bind Calls.rangeBounds) scalars

theorem sequenceSource_relocate (rename : Nat → Nat) (value : Value) :
    sequenceSource (relocateValue rename value) = relocateSource rename (sequenceSource value) := by
  cases value <;> rfl

theorem sequenceSource_within (limit : Nat) (value : Value) (inside : value.edge.Within limit) :
    SourceWithin limit (sequenceSource value) := by
  cases value <;> exact inside

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_range_start_relocates (name : String) (values : List Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.startRange name values body otherwise following env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.startRange name values body otherwise following env, stack, logical⟩ globals) := by
  cases tested : rangeBounds values with
  | error exception =>
    simp [relocateState, relocateWork, step, rangeBounds_relocate, tested, done, relocateStep,
      relocateCompletion, Except.map, protectGenerator, Function.comp_def, relocateFrame_inGenerator] <;> rfl
  | ok triple =>
    rcases triple with ⟨start, stop, stride⟩
    simp [relocateState, relocateWork, step, rangeBounds_relocate, tested, relocateStep, relocateStmt]

theorem step_range_arguments_nil (name : String) (value : Value) (done : List Value)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module logicalAnchors
        ⟨.value value, .rangeArguments name done [] body otherwise following env :: stack, logical⟩ globals =
      .next ⟨.startRange name (done ++ [value]) body otherwise following env, stack, logical⟩ := rfl

theorem step_range_arguments_cons (name : String) (value : Value) (done : List Value) (expression : Expr) (rest : List Expr)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module logicalAnchors
        ⟨.value value, .rangeArguments name done (expression :: rest) body otherwise following env :: stack, logical⟩ globals =
      .next ⟨.expr expression env, .rangeArguments name (done ++ [value]) rest body otherwise following env :: stack, logical⟩ := rfl

theorem step_for_range_nil (name : String) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module logicalAnchors
        ⟨.block (.forIn (.name name) (.call (.name "range") []) body otherwise :: following) env, stack, logical⟩ globals =
      .next ⟨.startRange name [] body otherwise following env, stack, logical⟩ := rfl

theorem step_for_range_cons (name : String) (expression : Expr) (rest : List Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module logicalAnchors
        ⟨.block (.forIn (.name name) (.call (.name "range") (expression :: rest)) body otherwise :: following) env, stack, logical⟩ globals =
      .next ⟨.expr expression env, .rangeArguments name [] rest body otherwise following env :: stack, logical⟩ := rfl

theorem step_range_arguments_relocates (name : String) (value : Value) (done : List Value) (rest : List Expr)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value value, .rangeArguments name done rest body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .rangeArguments name done rest body otherwise following env :: stack, logical⟩ globals) := by
  cases rest <;>
    simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step_range_arguments_nil,
      step_range_arguments_cons, relocateStep, List.map_append, List.map_nil]

theorem step_for_range_relocates (name : String) (expressions : List Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical
          ⟨.block (.forIn (.name name) (.call (.name "range") expressions) body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors
          ⟨.block (.forIn (.name name) (.call (.name "range") expressions) body otherwise :: following) env, stack, logical⟩ globals) := by
  cases expressions <;>
    simp only [relocateState, relocateWork, List.map_cons, relocateFrame, relocateStmt, step_for_range_nil,
      step_for_range_cons, relocateStep, List.map_nil]

/-- Expose only the dispatch relevant to a loop with one named target. -/
theorem step_for_name_dispatch (name : String) (iterable : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module logicalAnchors
      ⟨.block (.forIn (.name name) iterable body otherwise :: following) env, stack, logical⟩ globals =
      match iterable with
      | .dictionaryValuesIterable receiver =>
          .next ⟨.expr receiver env, .dictionaryValuesReceiver (.name name) body otherwise following env :: stack, logical⟩
      | .permutationsIterable expressions =>
          .next (argumentsState (.permutationStart (.name name) body otherwise following env) env [] expressions stack logical)
      | .combinationsIterable expressions =>
          .next (argumentsState (.combinationStart (.name name) body otherwise following env) env [] expressions stack logical)
      | .call (.name "range") expressions => match expressions with
          | [] => .next ⟨.startRange name [] body otherwise following env, stack, logical⟩
          | first :: rest =>
              .next ⟨.expr first env, .rangeArguments name [] rest body otherwise following env :: stack, logical⟩
      | _ => .next ⟨.expr iterable env, .sequence name body otherwise following env :: stack, logical⟩ := by
  cases iterable with
  | call function expressions =>
    cases function with
    | name functionName =>
      by_cases isRange : functionName = "range"
      · subst functionName
        cases expressions <;> rfl
      · simp [step, isRange]
    | _ => rfl
  | _ => rfl

/-- Dispatch also preserves lowered dictionary, permutation, and combination iterables. -/
theorem step_for_name_relocates (name : String) (iterable : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical
          ⟨.block (.forIn (.name name) iterable body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors
          ⟨.block (.forIn (.name name) iterable body otherwise :: following) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step_for_name_dispatch]
  split
  · simp only [relocateStep, relocateState, relocateWork, List.map_cons, relocateFrame]
  · rename_i original expressions
    cases expressions <;>
      simp only [argumentsState, relocateStep, relocateState, relocateWork, relocateRuntimeOperation,
        List.map_cons, List.map_nil, relocateFrame]
  · rename_i original expressions
    cases expressions <;>
      simp only [argumentsState, relocateStep, relocateState, relocateWork, relocateRuntimeOperation,
        List.map_cons, List.map_nil, relocateFrame]
  · split <;> simp only [relocateStep, relocateState, relocateWork, List.map_cons, List.map_nil, relocateFrame]
  · simp only [relocateStep, relocateState, relocateWork, List.map_cons, relocateFrame]

theorem step_sequence_start_relocates (layout : RuntimeLayout logical physical rename)
    (name : String) (value : Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (inside : value.edge.Within logical.length) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value value, .sequence name body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .sequence name body otherwise following env :: stack, logical⟩ globals) := by
  have paired := layout.sequence value inside
  cases read : Mutable.sequence value logical with
  | none => simp [relocateState, relocateWork, relocateFrame, step, run, paired, read, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := sequence_keeps_heap logical after value outcome read
    subst after
    cases outcome with
    | error exception =>
      simp [relocateState, relocateWork, relocateFrame, step, run, paired, read, done, relocateStep,
        relocateCompletion, Except.map, protectGenerator, Function.comp_def, relocateFrame_inGenerator] <;> rfl
    | ok items =>
      simp [relocateState, relocateWork, relocateFrame, step, run, paired, read, relocateStep,
        relocateStmt, Except.map, sequenceSource_relocate]

variable (heap : Mutable.Heap) (anchors : Nat)

theorem StateWithin.range_start (name : String) (values : List Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (globalsInside : GlobalsWithin heap.length globals)
    (inside : StateWithin ⟨.startRange name values body otherwise following env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.startRange name values body otherwise following env, stack, heap⟩ globals) := by
  cases tested : rangeBounds values with
  | error exception =>
    simp only [step, tested, done]
    apply protectGenerator_within
    exact ⟨globalsInside, by intro value impossible; cases impossible⟩
  | ok triple =>
    rcases triple with ⟨start, stop, stride⟩
    simp only [step, tested, protectGenerator_next, StepWithin]
    refine ⟨⟨inside.1.1, ?_⟩, inside.2⟩
    intro statement member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [StmtWithin] using And.intro inside.1.2.1 inside.1.2.2.1
    · exact inside.1.2.2.2.1 statement member

theorem StateWithin.range_arguments (name : String) (value : Value) (done : List Value) (rest : List Expr)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.value value, .rangeArguments name done rest body otherwise following env :: stack, heap⟩) :
    StepWithin (step module anchors ⟨.value value, .rangeArguments name done rest body otherwise following env :: stack, heap⟩ globals) := by
  have saved := inside.2 (.rangeArguments name done rest body otherwise following env) (by simp)
  simp only [FrameWithin] at saved
  have valuesInside : ∀ item ∈ done ++ [value], item.edge.Within heap.length := by
    simpa only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq] using
      And.intro saved.2.2.2.2 inside.1
  have stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame :=
    fun frame member => inside.2 frame (by simp [member])
  cases rest with
  | nil =>
    rw [step_range_arguments_nil]
    exact ⟨⟨saved.1, saved.2.1, saved.2.2.1, saved.2.2.2.1, valuesInside⟩, stackInside⟩
  | cons expression rest =>
    rw [step_range_arguments_cons]
    refine ⟨saved.1, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [FrameWithin]
      exact ⟨saved.1, saved.2.1, saved.2.2.1, saved.2.2.2.1, valuesInside⟩
    · exact stackInside frame member

theorem StateWithin.for_range (name : String) (expressions : List Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin
      ⟨.block (.forIn (.name name) (.call (.name "range") expressions) body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors
      ⟨.block (.forIn (.name name) (.call (.name "range") expressions) body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 (.forIn (.name name) (.call (.name "range") expressions) body otherwise) (by simp)
  simp only [StmtWithin] at loopInside
  have restInside : ∀ statement ∈ following, StmtWithin heap.length statement :=
    fun statement member => inside.1.2 statement (by simp [member])
  cases expressions with
  | nil =>
    rw [step_for_range_nil]
    exact ⟨⟨inside.1.1, loopInside.1, loopInside.2, restInside, by simp⟩, inside.2⟩
  | cons expression rest =>
    rw [step_for_range_cons]
    refine ⟨inside.1.1, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [FrameWithin]
      exact ⟨inside.1.1, loopInside.1, loopInside.2, restInside, by simp⟩
    · exact inside.2 frame member

theorem StateWithin.for_name (name : String) (iterable : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.forIn (.name name) iterable body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors
      ⟨.block (.forIn (.name name) iterable body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 (.forIn (.name name) iterable body otherwise) (by simp)
  simp only [StmtWithin] at loopInside
  have restInside : ∀ statement ∈ following, StmtWithin heap.length statement :=
    fun statement member => inside.1.2 statement (by simp [member])
  have envInside := inside.1.1
  have stackInside := inside.2
  rw [step_for_name_dispatch]
  split
  · simpa only [StepWithin, StateWithin, WorkWithin, List.mem_cons, forall_eq_or_imp, FrameWithin] using
      And.intro envInside (And.intro (And.intro envInside (And.intro loopInside.1 (And.intro loopInside.2 restInside))) stackInside)
  · rename_i original expressions
    cases expressions <;>
      simp [argumentsState, StepWithin, StateWithin, WorkWithin, FrameWithin, OperationWithin, envInside] <;>
      exact ⟨⟨loopInside.1, loopInside.2, restInside⟩, stackInside⟩
  · rename_i original expressions
    cases expressions <;>
      simp [argumentsState, StepWithin, StateWithin, WorkWithin, FrameWithin, OperationWithin, envInside] <;>
      exact ⟨⟨loopInside.1, loopInside.2, restInside⟩, stackInside⟩
  · split
    · exact ⟨⟨envInside, loopInside.1, loopInside.2, restInside, by simp⟩, stackInside⟩
    · simpa [StepWithin, StateWithin, WorkWithin, FrameWithin] using
        And.intro envInside (And.intro (And.intro envInside (And.intro loopInside.1 (And.intro loopInside.2 restInside))) stackInside)
  · simpa only [StepWithin, StateWithin, WorkWithin, List.mem_cons, forall_eq_or_imp, FrameWithin] using
      And.intro envInside (And.intro (And.intro envInside (And.intro loopInside.1 (And.intro loopInside.2 restInside))) stackInside)

theorem StateWithin.sequence_start (name : String) (value : Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (globalsInside : GlobalsWithin heap.length globals)
    (inside : StateWithin ⟨.value value, .sequence name body otherwise following env :: stack, heap⟩) :
    StepWithin (step module anchors ⟨.value value, .sequence name body otherwise following env :: stack, heap⟩ globals) := by
  have saved := inside.2 (.sequence name body otherwise following env) (by simp)
  simp only [FrameWithin] at saved
  have stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame :=
    fun frame member => inside.2 frame (by simp [member])
  cases read : Mutable.sequence value heap with
  | none => simp [step, run, read, StepWithin, protectGenerator]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := sequence_keeps_heap heap after value outcome read
    subst after
    cases outcome with
    | error exception =>
      simp only [step, run, read, done]
      apply protectGenerator_within
      exact ⟨globalsInside, by intro result impossible; cases impossible⟩
    | ok items =>
      simp only [step, run, read, protectGenerator_next, StepWithin]
      refine ⟨⟨saved.1, ?_⟩, stackInside⟩
      intro statement member
      rcases List.mem_cons.mp member with rfl | member
      · simp only [StmtWithin]
        exact ⟨sequenceSource_within heap.length value inside.1, saved.2.1, saved.2.2.1⟩
      · exact saved.2.2.2 statement member

/-- Collect all remaining values before checking range bounds, retaining each expression's effects. -/
theorem range_arguments_reach {globals : Mutable.Globals} {module : Module} {env : Env}
    {expressions : List Expr} {heap finalHeap : Mutable.Heap} {values : List Value}
    (evaluated : Evaluates.Arguments (globals := globals) module env expressions heap values finalHeap)
    (name : String) (done : List Value) (value : Value) (body otherwise following : List Stmt)
    (anchors : Nat) (stack : List Frame) :
    Reaches (globals := globals) module anchors
      ⟨.value value, .rangeArguments name done expressions body otherwise following env :: stack, heap⟩
      ⟨.startRange name (done ++ value :: values) body otherwise following env, stack, finalHeap⟩ := by
  induction evaluated generalizing done value with
  | nil => exact .next (step_range_arguments_nil module _ anchors name value done body otherwise following env stack _) .refl
  | cons head tail ih =>
    apply Reaches.next (step_range_arguments_cons module _ anchors name value done _ _ body otherwise following env stack _)
    apply (head anchors _).trans
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using ih (done ++ [value]) _

/-- Reach conversion even when an earlier argument will fail its eventual index check. -/
theorem for_range_reach {globals : Mutable.Globals} {module : Module} {env : Env}
    {expressions : List Expr} {heap finalHeap : Mutable.Heap} {values : List Value}
    (evaluated : Evaluates.Arguments (globals := globals) module env expressions heap values finalHeap)
    (name : String) (body otherwise following : List Stmt) (anchors : Nat) (stack : List Frame) :
    Reaches (globals := globals) module anchors
      ⟨.block (.forIn (.name name) (.call (.name "range") expressions) body otherwise :: following) env, stack, heap⟩
      ⟨.startRange name values body otherwise following env, stack, finalHeap⟩ := by
  cases evaluated with
  | nil => exact .next (step_for_range_nil module _ anchors name body otherwise following env stack _) .refl
  | cons head tail =>
    apply Reaches.next (step_for_range_cons module _ anchors name _ _ body otherwise following env stack _)
    apply (head anchors _).trans
    exact range_arguments_reach tail name [] _ body otherwise following anchors stack

end FormalSW.PyAst.HeapCalls.Relocation
