import lang.py.FormalSW.SetCalls
import lang.py.FormalSW.HeapRuntimeCostControl

/-! Runtime bounds for every permitted set traversal order. Ordinary execution
keeps the heap interpreter's tariffs. Scalar-set acquisition pays for the
iterator snapshot; each iterator step conservatively allows a scan of the
remaining representatives. Choice schedules describe order, not program data. -/
namespace FormalSW.PyAst.SetCalls.Runtime
open PrimitiveWork

def iteratorCharge (arithmetic : Arithmetic) (state : HeapCalls.State) : Option Nat :=
  match state.work, state.stack with
  | .value (.ref address), .sequence _ _ _ _ _ :: _ =>
      match state.heap[address]? with
      | some (.set items) => some (items.length + 2)
      | _ => none
  | .block (.setStepLoop _ address original remaining _ _ :: _) _, _ =>
      match state.heap[address]? with
      | some (.set current) => some (remaining.length +
          integer arithmetic current.length + integer arithmetic original.length + 3)
      | _ => none
  | _, _ => none

def charge (arithmetic : Arithmetic) (module : Module) (state : State)
    (maps : MapRepresentation := .collisionChain) : Option Nat :=
  match HeapCalls.Runtime.charge arithmetic module state.core maps with
  | some amount => some amount
  | none => iteratorCharge arithmetic state.core

def potential (state : State) : Nat := HeapCalls.Runtime.potential state.core

abbrev Reaches (arithmetic : Arithmetic) (module : Module) (anchors : Nat)
    (choices : ChoiceSchedule) (initial : State) (budget : Nat) (final : State)
    (globals : Mutable.Globals := []) :=
  RuntimeCost.Amortized.Reaches (step (globals := globals) module anchors choices)
    (charge arithmetic module) potential initial budget final

def TimeBound (arithmetic : Arithmetic) (module : Module) (name : String)
    (values : List Mutable.Value) (heap : Mutable.Heap) (bound : Nat)
    (maps : MapRepresentation := .collisionChain) (globals : Mutable.Globals := []) : Prop :=
  ∀ choices, RuntimeCost.TimeBound ((call module name values heap globals).run choices).execution
    (charge arithmetic module · maps) bound

/-- A single constant and threshold must work for every input and every order. -/
def IsBigO (arithmetic : Arithmetic) (module : Module) (name : String)
    (inputs : ι → List Mutable.Value) (heaps : ι → Mutable.Heap) (domain : ι → Prop)
    (size : ι → Nat) (bound : Nat → Nat) (maps : MapRepresentation := .collisionChain)
    (globals : ι → Mutable.Globals := fun _ => []) : Prop :=
  RuntimeCost.IsBigO
    (fun pair : ι × ChoiceSchedule =>
      ((call module name (inputs pair.1) (heaps pair.1) (globals pair.1)).run pair.2).execution)
    (fun _ state => charge arithmetic module state maps)
    (fun pair => domain pair.1) (fun pair => size pair.1) bound

theorem charge_of_heap
    (measured : HeapCalls.Runtime.charge arithmetic module core maps = some amount) :
    charge arithmetic module ⟨core, used⟩ maps = some amount := by
  simp only [charge, measured]

/-- Lift an ordinary charged trace without advancing the order schedule. -/
theorem lift_trace
    (run : RuntimeCost.Reaches (HeapCalls.step (globals := globals) module anchors)
      (HeapCalls.Runtime.charge arithmetic module) initial cost final) :
    RuntimeCost.Reaches (step (globals := globals) module anchors choices)
      (charge arithmetic module) ⟨initial, used⟩ cost ⟨final, used⟩ := by
  induction run with
  | refl => exact .refl
  | next transition measured _ ih =>
      exact .next (by simp only [step, transition, liftStep])
        (charge_of_heap measured) ih

/-- Existing helper proofs retain their complete cost and heap-potential bound. -/
theorem lift_heap
    (run : HeapCalls.Runtime.Reaches (globals := globals) arithmetic module anchors initial budget final) :
    Reaches (globals := globals) arithmetic module anchors choices ⟨initial, used⟩ budget ⟨final, used⟩ := by
  obtain ⟨cost, trace, paid⟩ := run
  exact ⟨cost, lift_trace trace, paid⟩

/-- Retained input objects retain their potential, so their credits cannot
subsidize the bound. The final value state also pays its terminal tariff. -/
theorem trace_timeBound_append
    (run : Reaches (globals := globals) arithmetic module heap.length choices
      ⟨⟨.operation (.call name) values, [], heap⟩, 0⟩ budget
      ⟨⟨.value value, [], heap ++ extra⟩, used⟩) :
    RuntimeCost.TimeBound ((call module name values heap globals).run choices).execution
      (charge arithmetic module) (budget + 1) := by
  obtain ⟨cost, steps, paid⟩ := run
  have terminal : RuntimeCost.Finishes (step (globals := globals) module heap.length choices)
      (charge arithmetic module) ⟨⟨.value value, [], heap ++ extra⟩, used⟩ 1
      (.ok ⟨.ok value, globals, heap ++ extra, heap.length⟩) := .done rfl rfl
  refine ⟨cost + 1, _, steps.finishes terminal, ?_⟩
  simp only [potential, HeapCalls.Runtime.potential, HeapCalls.Runtime.heapPotential,
    List.map_append, List.sum_append] at paid
  omega

end FormalSW.PyAst.SetCalls.Runtime
