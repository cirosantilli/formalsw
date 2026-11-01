import lang.py.FormalSW.MachinePositional
import lang.py.FormalSW.MachineEnumerate

/-! Source for-loop dispatch retains target shape and iterator-specialization order. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

set_option maxHeartbeats 1000000 in
theorem step_for_unpack_dispatch (asList : Bool) (targets : List Expr) (iterable : Expr)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module logicalAnchors
      ⟨.block (.forIn (if asList then .list targets else .tuple targets) iterable body otherwise :: following) env, stack, logical⟩ globals =
      match iterable with
      | .dictionaryValuesIterable receiver => .next ⟨.expr receiver env,
          .dictionaryValuesReceiver (if asList then .list targets else .tuple targets) body otherwise following env :: stack, logical⟩
      | .permutationsIterable expressions => .next (argumentsState
          (.permutationStart (if asList then .list targets else .tuple targets) body otherwise following env) env [] expressions stack logical)
      | .combinationsIterable expressions => .next (argumentsState
          (.combinationStart (if asList then .list targets else .tuple targets) body otherwise following env) env [] expressions stack logical)
      | _ => match targets, iterable with
          | [.name index, .name name], .call (.name "enumerate") [source] => .next ⟨.expr source env,
              .enumerateSource index name (.constant (.int 0)) body otherwise following env :: stack, logical⟩
          | [.name index, .name name], .call (.name "enumerate") [source, start] => .next ⟨.expr source env,
              .enumerateSource index name start body otherwise following env :: stack, logical⟩
          | _, _ => match Calls.targetNames targets with
              | some names => .next ⟨.expr iterable env, .unpackSequence names body otherwise following env :: stack, logical⟩
              | none => .next ⟨.block (.forIn (.name "$formalsw.unpack") iterable
                  (comprehensionTargetBody (.tuple targets) body) otherwise :: following) env, stack, logical⟩ := by
  cases asList <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    cases iterable with
    | call function expressions =>
      cases function with
      | name functionName =>
        by_cases isEnumerate : functionName = "enumerate"
        · subst functionName
          cases targets with
          | nil => rfl
          | cons first rest =>
            cases first <;> try rfl
            cases rest with
            | nil => rfl
            | cons second tail =>
              cases second <;> try rfl
              cases tail with
              | cons _ _ => simp only [step]; split <;> simp_all
              | nil =>
                cases expressions with
                | nil => rfl
                | cons source rest =>
                  cases rest with
                  | nil => rfl
                  | cons start rest => cases rest <;> rfl
        · cases named : Calls.targetNames targets <;> simp [step, isEnumerate, named]
      | _ => cases named : Calls.targetNames targets <;> simp only [step, named, protectGenerator_next]
    | _ => first | rfl | (cases named : Calls.targetNames targets <;> simp only [step, named, protectGenerator_next])

theorem step_for_unpack_relocates (asList : Bool) (targets : List Expr) (iterable : Expr)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical
          ⟨.block (.forIn (if asList then .list targets else .tuple targets) iterable body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors
          ⟨.block (.forIn (if asList then .list targets else .tuple targets) iterable body otherwise :: following) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step_for_unpack_dispatch]
  split
  · simp only [relocateStep, relocateState, relocateWork, List.map_cons, relocateFrame]
  · rename_i expressions
    cases expressions <;> simp only [argumentsState, relocateStep, relocateState, relocateWork, relocateRuntimeOperation,
      List.map_cons, List.map_nil, relocateFrame]
  · rename_i expressions
    cases expressions <;> simp only [argumentsState, relocateStep, relocateState, relocateWork, relocateRuntimeOperation,
      List.map_cons, List.map_nil, relocateFrame]
  · split
    · simp only [relocateStep, relocateState, relocateWork, List.map_cons, relocateFrame]
    · simp only [relocateStep, relocateState, relocateWork, List.map_cons, relocateFrame]
    · split <;> simp only [relocateStep, relocateState, relocateWork, List.map_cons, relocateFrame,
        comprehensionTargetBody, relocateStmt]

def flatForTarget : Expr → Bool
  | .name _ | .tuple _ | .list _ => true
  | _ => false

set_option maxHeartbeats 1000000 in
theorem step_for_other_dispatch (target iterable : Expr) (other : flatForTarget target = false)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module logicalAnchors ⟨.block (.forIn target iterable body otherwise :: following) env, stack, logical⟩ globals =
      match iterable with
      | .dictionaryValuesIterable receiver => .next ⟨.expr receiver env,
          .dictionaryValuesReceiver target body otherwise following env :: stack, logical⟩
      | .permutationsIterable expressions => .next (argumentsState
          (.permutationStart target body otherwise following env) env [] expressions stack logical)
      | .combinationsIterable expressions => .next (argumentsState
          (.combinationStart target body otherwise following env) env [] expressions stack logical)
      | _ => .unsupported := by
  cases target <;> simp only [flatForTarget] at other <;> try contradiction
  all_goals cases iterable <;> try rfl
  all_goals
    rename_i function expressions
    cases function <;> try rfl
    all_goals simp only [step, protectGenerator_unsupported]

theorem step_for_other_relocates (target iterable : Expr) (other : flatForTarget target = false)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.forIn target iterable body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.forIn target iterable body otherwise :: following) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step_for_other_dispatch _ _ _ target iterable other]
  split
  · simp only [relocateStep, relocateState, relocateWork, List.map_cons, relocateFrame]
  · rename_i expressions
    cases expressions <;> simp only [argumentsState, relocateStep, relocateState, relocateWork, relocateRuntimeOperation,
      List.map_cons, List.map_nil, relocateFrame]
  · rename_i expressions
    cases expressions <;> simp only [argumentsState, relocateStep, relocateState, relocateWork, relocateRuntimeOperation,
      List.map_cons, List.map_nil, relocateFrame]
  · rfl

/-- All source target and iterable shapes, including unsupported combinations. -/
theorem step_for_relocates (target iterable : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.forIn target iterable body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.forIn target iterable body otherwise :: following) env, stack, logical⟩ globals) := by
  cases target with
  | name name => exact step_for_name_relocates module logical physical rename logicalAnchors physicalAnchors name iterable body otherwise following env stack globals
  | tuple targets => exact step_for_unpack_relocates module logical physical rename logicalAnchors physicalAnchors false targets iterable body otherwise following env stack globals
  | list targets => exact step_for_unpack_relocates module logical physical rename logicalAnchors physicalAnchors true targets iterable body otherwise following env stack globals
  | _ => exact step_for_other_relocates module logical physical rename logicalAnchors physicalAnchors _ iterable rfl body otherwise following env stack globals


variable (heap : Mutable.Heap) (anchors : Nat)

theorem StateWithin.for_unpack (asList : Bool) (targets : List Expr) (iterable : Expr)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.forIn (if asList then .list targets else .tuple targets)
      iterable body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.forIn (if asList then .list targets else .tuple targets)
      iterable body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  simp only [StmtWithin] at loopInside
  have restInside : ∀ statement ∈ following, StmtWithin heap.length statement :=
    fun statement member => inside.1.2 statement (List.mem_cons_of_mem _ member)
  have envInside := inside.1.1
  have stackInside := inside.2
  rw [step_for_unpack_dispatch]
  split
  · simpa only [StepWithin, StateWithin, WorkWithin, List.mem_cons, forall_eq_or_imp, FrameWithin] using
      And.intro envInside (And.intro (And.intro envInside (And.intro loopInside.1 (And.intro loopInside.2 restInside))) stackInside)
  · rename_i expressions
    cases expressions <;>
      simp [argumentsState, StepWithin, StateWithin, WorkWithin, FrameWithin, OperationWithin, envInside] <;>
      exact ⟨⟨loopInside.1, loopInside.2, restInside⟩, stackInside⟩
  · rename_i expressions
    cases expressions <;>
      simp [argumentsState, StepWithin, StateWithin, WorkWithin, FrameWithin, OperationWithin, envInside] <;>
      exact ⟨⟨loopInside.1, loopInside.2, restInside⟩, stackInside⟩
  · split
    · simpa only [StepWithin, StateWithin, WorkWithin, List.mem_cons, forall_eq_or_imp, FrameWithin] using
        And.intro envInside (And.intro (And.intro envInside (And.intro loopInside.1 (And.intro loopInside.2 restInside))) stackInside)
    · simpa only [StepWithin, StateWithin, WorkWithin, List.mem_cons, forall_eq_or_imp, FrameWithin] using
        And.intro envInside (And.intro (And.intro envInside (And.intro loopInside.1 (And.intro loopInside.2 restInside))) stackInside)
    · split
      · simpa only [StepWithin, StateWithin, WorkWithin, List.mem_cons, forall_eq_or_imp, FrameWithin] using
          And.intro envInside (And.intro (And.intro envInside (And.intro loopInside.1 (And.intro loopInside.2 restInside))) stackInside)
      · exact ⟨⟨envInside, by
          simpa only [List.mem_cons, forall_eq_or_imp, StmtWithin, comprehensionTargetBody,
            and_true, true_and] using And.intro (And.intro loopInside.1 loopInside.2) restInside⟩, stackInside⟩

theorem StateWithin.for_other (target iterable : Expr) (other : flatForTarget target = false)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.forIn target iterable body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.forIn target iterable body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  simp only [StmtWithin] at loopInside
  have restInside : ∀ statement ∈ following, StmtWithin heap.length statement :=
    fun statement member => inside.1.2 statement (List.mem_cons_of_mem _ member)
  have envInside := inside.1.1
  have stackInside := inside.2
  rw [step_for_other_dispatch _ _ _ target iterable other]
  split
  · simpa only [StepWithin, StateWithin, WorkWithin, List.mem_cons, forall_eq_or_imp, FrameWithin] using
      And.intro envInside (And.intro (And.intro envInside (And.intro loopInside.1 (And.intro loopInside.2 restInside))) stackInside)
  · rename_i expressions
    cases expressions <;>
      simp [argumentsState, StepWithin, StateWithin, WorkWithin, FrameWithin, OperationWithin, envInside] <;>
      exact ⟨⟨loopInside.1, loopInside.2, restInside⟩, stackInside⟩
  · rename_i expressions
    cases expressions <;>
      simp [argumentsState, StepWithin, StateWithin, WorkWithin, FrameWithin, OperationWithin, envInside] <;>
      exact ⟨⟨loopInside.1, loopInside.2, restInside⟩, stackInside⟩
  · trivial

theorem StateWithin.forIn (target iterable : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.forIn target iterable body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.forIn target iterable body otherwise :: following) env, stack, heap⟩ globals) := by
  cases target with
  | name name => exact StateWithin.for_name module heap anchors name iterable body otherwise following env stack globals inside
  | tuple targets => exact StateWithin.for_unpack module heap anchors false targets iterable body otherwise following env stack globals inside
  | list targets => exact StateWithin.for_unpack module heap anchors true targets iterable body otherwise following env stack globals inside
  | _ => exact StateWithin.for_other module heap anchors _ iterable rfl body otherwise following env stack globals inside

end FormalSW.PyAst.HeapCalls.Relocation
