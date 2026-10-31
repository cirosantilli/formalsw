import lang.py.FormalSW.CoreFrame
import lang.py.FormalSW.MachineBounds

/-! Derive write separation from an address map whose image excludes a private cell. -/
namespace FormalSW.PyAst.HeapCalls.Framing
open Mutable Mutable.Relocation HeapCalls.Relocation
set_option Elab.async false

theorem receiverTargets_relocates (rename : Nat → Nat) (values : List Value) :
    Heapq.receiverTargets (values.map (relocateValue rename)) = (Heapq.receiverTargets values).map rename := by
  cases values with
  | nil => rfl
  | cons value rest => cases value <;> rfl

theorem receiverTargets_within (limit : Nat) (values : List Value)
    (inside : ∀ value ∈ values, value.edge.Within limit) (address : Nat)
    (member : address ∈ Heapq.receiverTargets values) : address < limit := by
  cases values with
  | nil => cases member
  | cons value rest =>
    cases value with
    | scalar scalar => cases member
    | ref receiver =>
      have same : address = receiver := List.mem_singleton.mp member
      subst address
      exact inside (.ref receiver) (List.mem_cons_self ..)

theorem operationTargets_relocates (rename : Nat → Nat) (operation : Operation) (values : List Value) :
    operationTargets (relocateRuntimeOperation rename operation) (values.map (relocateValue rename)) =
      (operationTargets operation values).map rename := by
  cases operation <;> simp only [operationTargets, Heapq.primitiveTargets, relocateRuntimeOperation,
    relocateOperation, receiverTargets_relocates, List.map_nil, List.map_cons]
  case builtin builtin => cases builtin <;> simp only [Heapq.builtinTargets, receiverTargets_relocates, List.map_nil]

theorem operationTargets_within (limit : Nat) (operation : Operation) (values : List Value)
    (operationInside : OperationWithin limit operation) (valuesInside : ∀ value ∈ values, value.edge.Within limit)
    (address : Nat) (member : address ∈ operationTargets operation values) : address < limit := by
  cases operation <;> simp only [operationTargets, Heapq.primitiveTargets] at member
  all_goals first
    | exact False.elim (List.not_mem_nil member)
    | (obtain rfl := List.mem_singleton.mp member; exact operationInside)
    | exact receiverTargets_within limit values valuesInside address member
    | skip
  case builtin builtin =>
    cases builtin <;> simp only [Heapq.builtinTargets] at member
    all_goals first
      | exact False.elim (List.not_mem_nil member)
      | exact receiverTargets_within limit values valuesInside address member

theorem relocateValue_separate (rename : Nat → Nat) (limit address : Nat) (value : Value)
    (inside : value.edge.Within limit) (outside : ∀ source < limit, rename source ≠ address) :
    relocateValue rename value ≠ .ref address := by
  cases value with
  | scalar scalar => intro impossible; cases impossible
  | ref source => exact fun equal => outside source inside (Value.ref.inj equal)

theorem relocateFrame_separate (rename : Nat → Nat) (limit address : Nat) (frame : Frame)
    (inside : FrameWithin limit frame) (outside : ∀ source < limit, rename source ≠ address) :
    FrameSeparate address (relocateFrame rename frame) := by
  cases frame <;> simp only [relocateFrame, FrameSeparate]
  all_goals first | trivial | skip
  all_goals simp only [FrameWithin] at inside
  case writeAttribute receiver name rest env => exact relocateValue_separate rename limit address receiver inside.1 outside
  case writeItem receiver index rest env => exact relocateValue_separate rename limit address receiver inside.1 outside
  case binaryRight op left inPlace => exact fun _ => relocateValue_separate rename limit address left inside outside

/-- This is a one-state rule: a growing execution must also keep later address maps disjoint. -/
theorem relocateState_separate (rename : Nat → Nat) (physical : Heap) (address : Nat) (state : State)
    (inside : StateWithin state) (outside : ∀ source < state.heap.length, rename source ≠ address) :
    StateSeparate address (relocateState rename physical state) := by
  rcases state with ⟨work, stack, heap⟩
  cases work <;> first | trivial | skip
  case operation operation values =>
    change ∀ receiver ∈ operationTargets (relocateRuntimeOperation rename operation)
      (values.map (relocateValue rename)), receiver ≠ address
    rw [operationTargets_relocates]
    intro receiver member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    exact outside source (operationTargets_within heap.length operation values inside.1.1 inside.1.2 source sourceMember)
  case value value =>
    cases stack with
    | nil => simp [StateSeparate, relocateState, relocateWork]
    | cons frame rest =>
      intro selected member
      have same : selected = relocateFrame rename frame := by simpa [relocateState] using (Option.mem_def.mp member).symm
      subst selected
      exact relocateFrame_separate rename heap.length address frame (inside.2 frame (List.mem_cons_self ..)) outside

theorem relocated_step_cell (module : Module) (rename : Nat → Nat) (physical : Heap)
    (address anchors : Nat) (object : Object) (state : State) (globals : Globals)
    (inside : StateWithin state) (outside : ∀ source < state.heap.length, rename source ≠ address)
    (saved : SavedCell address object physical) :
    RetainsCell address object (step module anchors (relocateState rename physical state) globals) :=
  step_cell module address anchors object _ globals (relocateState_separate rename physical address state inside outside) saved

end FormalSW.PyAst.HeapCalls.Framing
