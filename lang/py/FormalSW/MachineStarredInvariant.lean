import lang.py.FormalSW.MachineGeneratorEntry

/-! Starred argument continuations preserve immediate snapshots and shared references. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem starItems_sequence_or_unsupported (heap : Mutable.Heap) (value : Value) :
    starItems value heap = Mutable.sequence value heap ∨ starItems value heap = none := by
  cases value with
  | scalar scalar => cases scalar <;> simp [starItems, Mutable.sequence, Mutable.error]
  | ref address =>
    cases found : heap[address]? with
    | none => simp [starItems, found, Mutable.unsupported]
    | some object => cases object <;> simp [starItems, Mutable.sequence, found, Mutable.unsupported]

theorem starItems_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (value : Value)
    (inside : value.edge.Within logical.length) :
    starItems (relocateValue rename value) physical =
      (starItems value logical).map
        (fun pair => (pair.1.map (List.map (relocateValue rename)), physical)) := by
  cases value with
  | scalar scalar =>
    cases scalar <;> simp [starItems, Mutable.sequence, relocateValue, Mutable.error,
      Except.map, List.map_map, Function.comp_def]
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;>
      simp only [object, relocateObject] at moved <;>
      simp [starItems, Mutable.sequence, relocateValue, found, object, moved, Mutable.unsupported,
        Except.map, List.map_map, Function.comp_def]

theorem starItems_keeps_heap (heap after : Mutable.Heap) (value : Value)
    (outcome : Except ExceptionObject (List Value))
    (executed : starItems value heap = some (outcome, after)) : after = heap := by
  rcases starItems_sequence_or_unsupported heap value with same | unsupported
  · exact sequence_keeps_heap heap after value outcome (same ▸ executed)
  · simp [unsupported] at executed

theorem starItems_bounded (heap after : Mutable.Heap) (closed : Closed heap) (value : Value)
    (items : List Value) (executed : starItems value heap = some (.ok items, after)) :
    ∀ item ∈ items, item.edge.Within heap.length := by
  rcases starItems_sequence_or_unsupported heap value with same | unsupported
  · exact sequence_items_within heap after closed value items (same ▸ executed)
  · simp [unsupported] at executed

theorem step_starredArguments_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (operation : Operation)
    (done : List Value) (rest : List Expr) (env : Env) (starred : Bool)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .starredArguments operation done rest env starred :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .starredArguments operation done rest env starred :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .starredArguments operation done rest env starred :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have captured := inside.2 (.starredArguments operation done rest env starred) (by simp)
  simp only [FrameWithin] at captured
  have stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame :=
    fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)
  have enter (items : List Value) (bounded : ∀ item ∈ items, item.edge.Within logical.length) :=
    expanded_arguments_entry_preserves logical physical rename physicalAnchors operation env (done ++ items)
      rest stack layout captured.2.1 captured.1 (by
        intro item member
        rcases List.mem_append.mp member with member | member
        · exact captured.2.2 item member
        · exact bounded item member) stackInside
  cases starred with
  | false =>
    have raw := (enter [value] (by simpa using inside.1)).protectGenerator
      (.starredArguments operation done rest env false :: stack) inside.2
    simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame,
      Bool.false_eq_true, if_false, List.map_append, List.map_nil] using raw
  | true =>
    have paired := starItems_relocates logical physical rename layout.runtime value inside.1
    cases executed : starItems value logical with
    | none =>
      apply Preserves.unchanged layout <;>
        simp [step, run, executed, paired, protectGenerator, StepHeap, StepWithin,
          relocateState, relocateWork, relocateFrame, relocateStep]
    | some pair =>
      rcases pair with ⟨outcome, after⟩
      have same := starItems_keeps_heap logical after value outcome executed
      subst after
      cases outcome with
      | error exception =>
        have raw : Preserves logical physical rename physicalAnchors
            (HeapCalls.done logicalAnchors logical (.error exception) globals)
            (HeapCalls.done physicalAnchors physical (.error exception) (relocateGlobals rename globals)) := by
          apply Preserves.unchanged layout
          · rfl
          · exact ⟨globalsInside, by intro _ impossible; cases impossible⟩
          · rfl
        simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame,
          if_true, run, executed, paired, Option.map_some, Except.map] using
          raw.protectGenerator (.starredArguments operation done rest env true :: stack) inside.2
      | ok items =>
        have raw := (enter items (starItems_bounded logical logical layout.closed value items executed)).protectGenerator
          (.starredArguments operation done rest env true :: stack) inside.2
        simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame,
          if_true, run, executed, paired, Option.map_some, Except.map, List.map_append] using raw

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_starredArguments_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (value : Mutable.Value) (operation : Operation) (done : List Mutable.Value) (rest : List Expr)
    (env : HeapCalls.Env) (starred : Bool) (stack : List HeapCalls.Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin logical.length (.running
      ⟨⟨.value value, .starredArguments operation done rest env starred :: stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running
        ⟨⟨.value value, .starredArguments operation done rest env starred :: stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running
          ⟨⟨.value value, .starredArguments operation done rest env starred :: stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running
      ⟨⟨.value value, .starredArguments operation done rest env starred :: stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_starredArguments_preserves module logical physical rename logicalAnchors physicalAnchors
      value operation done rest env starred stack globals layout ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
