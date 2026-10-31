import lang.py.FormalSW.IteratorFrame
import lang.py.FormalSW.FrameIsolation
import lang.py.FormalSW.IteratorContinuation
import lang.py.FormalSW.IteratorInvariant

/-! Compose private-cell frames with suspended consumers and disjoint relocated states. -/
namespace FormalSW.PyAst.IteratorCalls.Framing
open Mutable Mutable.Relocation
set_option Elab.async false

theorem appendResumes_cell (address : Nat) (object : Object) (suffix : List Resume) (state : State) :
    StateCell address object (appendResumes suffix state) = StateCell address object state := by
  cases state with
  | running core resumes => rfl
  | completed outcome used resumes => cases outcome <;> rfl

theorem appendResumes_separate (address : Nat) (suffix : List Resume) (state : State) :
    StateSeparate address (appendResumes suffix state) = StateSeparate address state := by
  cases state <;> rfl

/-- A saved consumer may access the protected object after this prefix returns. -/
theorem SeparatedReaches.append_resumes {module : Module} {anchors address : Nat} {choices : ChoiceSchedule}
    {globals : Globals} {initial final : State}
    (path : SeparatedReaches module anchors address choices globals initial final) (suffix : List Resume) :
    SeparatedReaches module anchors address choices globals (appendResumes suffix initial) (appendResumes suffix final) := by
  induction path with
  | refl => exact .refl
  | next separate transition path ih =>
    exact .next (by simpa only [appendResumes_separate] using separate) (step_next_append transition suffix) ih

theorem relocateState_separate (rename : Nat → Nat) (logical physical : Heap) (address anchors : Nat)
    (state : State) (heap : Relocation.StateHeap logical state) (inside : Relocation.StateWithin logical.length state)
    (outside : ∀ source < logical.length, rename source ≠ address) :
    StateSeparate address (Relocation.relocateState rename physical anchors state) := by
  cases state with
  | completed outcome used resumes => trivial
  | running core resumes =>
    have same : core.core.heap = logical := heap
    subst logical
    exact HeapCalls.Framing.relocateState_separate rename physical address core.core ⟨inside.1, inside.2.1⟩ outside

theorem relocateState_cell (rename : Nat → Nat) (physical : Heap) (address anchors : Nat) (object : Object)
    (state : State) (saved : SavedCell address object physical) :
    StateCell address object (Relocation.relocateState rename physical anchors state) := by
  cases state with
  | running core resumes => exact saved
  | completed outcome used resumes => cases outcome <;> first | exact saved | trivial

/-- The address-exclusion premise is local to this step, rather than an assertion about future maps. -/
theorem relocated_step_cell (module : Module) (rename : Nat → Nat) (logical physical : Heap)
    (address anchors : Nat) (object : Object) (choices : ChoiceSchedule) (globals : Globals)
    (state : State) (heap : Relocation.StateHeap logical state) (inside : Relocation.StateWithin logical.length state)
    (outside : ∀ source < logical.length, rename source ≠ address) (saved : SavedCell address object physical) :
    RetainsCell address object (step module anchors choices (Relocation.relocateState rename physical anchors state) globals) :=
  step_cell module address anchors object _ choices globals
    (relocateState_separate rename logical physical address anchors state heap inside outside)
    (relocateState_cell rename physical address anchors object state saved)

end FormalSW.PyAst.IteratorCalls.Framing
