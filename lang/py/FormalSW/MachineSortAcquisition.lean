import lang.py.FormalSW.MachineGeneratorEntry
import lang.py.FormalSW.MachineRunInvariant

/-! Key evaluation retains sorting snapshots and live extremum sources. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem sortedItems_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (value : Value)
    (inside : value.edge.Within logical.length) :
    sortedItems (relocateValue rename value) physical =
      (sortedItems value logical).map
        (fun pair => (pair.1.map (List.map (relocateValue rename)), physical)) := by
  cases value with
  | scalar scalar => exact layout.sequence (.scalar scalar) inside
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;>
      simp only [object, relocateObject] at moved <;>
      simp [sortedItems, Mutable.sequence, relocateValue, found, object, moved, Mutable.unsupported,
        Except.map, List.map_map, Function.comp_def]

theorem sortedItems_keeps_heap (heap after : Mutable.Heap) (value : Value)
    (outcome : Except ExceptionObject (List Value))
    (executed : sortedItems value heap = some (outcome, after)) : after = heap := by
  cases value with
  | scalar scalar => exact sequence_keeps_heap heap after (.scalar scalar) outcome executed
  | ref address =>
    cases found : heap[address]? with
    | none => simp [sortedItems, Mutable.sequence, found, Mutable.unsupported] at executed
    | some object =>
      cases object <;> simp [sortedItems, Mutable.sequence, found, Mutable.unsupported] at executed
      all_goals exact executed.2.symm

theorem sortedItems_bounded (heap after : Mutable.Heap) (closed : Closed heap) (value : Value)
    (items : List Value) (executed : sortedItems value heap = some (.ok items, after)) :
    ∀ item ∈ items, item.edge.Within heap.length := by
  cases value with
  | scalar scalar => exact sequence_items_within heap after closed (.scalar scalar) items executed
  | ref address =>
    cases found : heap[address]? with
    | none => simp [sortedItems, Mutable.sequence, found, Mutable.unsupported] at executed
    | some object =>
      have old := closed object (List.mem_of_getElem? found)
      cases object with
      | dict entries =>
        simp [sortedItems, found] at executed
        rcases executed with ⟨rfl, rfl⟩
        intro item member
        obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
        trivial
      | keyDict entries =>
        simp [sortedItems, found] at executed
        rcases executed with ⟨rfl, rfl⟩
        intro item member
        obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
        exact old entry.2.1 (List.mem_flatMap.mpr ⟨entry, present, by simp⟩)
      | list entries | tuple entries | bytearray entries =>
        exact sequence_items_within heap after closed (.ref address) items (by simpa [sortedItems, found] using executed)
      | _ => simp [sortedItems, found, Mutable.unsupported] at executed

theorem sortedStart_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (source reverse : Value)
    (sourceInside : source.edge.Within logical.length) (reverseInside : reverse.edge.Within logical.length) :
    sortedStart (relocateValue rename source) (relocateValue rename reverse) physical =
      (sortedStart source reverse logical).map
        (fun pair => (pair.1.map (fun result => (result.1.map (relocateValue rename), result.2)), physical)) := by
  have paired := sortedItems_relocates logical physical rename layout source sourceInside
  obtain ⟨flag, tested⟩ := truth_total logical reverse reverseInside
  have other := layout.truth reverse reverseInside
  rw [tested] at other
  cases read : sortedItems source logical with
  | none => simp [sortedStart, Mutable.eval_bind, read, paired]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have same := sortedItems_keeps_heap logical after source outcome read
    subst after
    cases outcome with
    | error exception => simp [sortedStart, Mutable.eval_bind, read, paired, Except.map]
    | ok items =>
      simp only [sortedStart, Mutable.eval_bind, paired, read, Option.map_some, Except.map]
      cases reverse with
      | scalar scalar =>
        simp only [relocateValue] at other
        simp [relocateValue, Mutable.eval_bind, tested, other, Except.map]
      | ref address =>
        have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem reverseInside
        have moved := layout.lookup address _ found
        simp only [relocateValue] at other
        cases object : logical[address] <;>
          simp only [object, relocateObject] at moved <;>
          simp [Mutable.eval_bind, relocateValue, found, object, moved, tested, other, Mutable.unsupported, Except.map]

theorem sortedStart_keeps_heap (heap after : Mutable.Heap) (source reverse : Value)
    (sourceInside : source.edge.Within heap.length) (reverseInside : reverse.edge.Within heap.length)
    (outcome : Except ExceptionObject (List Value × Bool))
    (executed : sortedStart source reverse heap = some (outcome, after)) : after = heap := by
  have paired := sortedStart_relocates heap heap id (RuntimeLayout.refl heap) source reverse sourceInside reverseInside
  simp only [relocateValue_id, executed, Option.map_some] at paired
  exact congrArg Prod.snd (Option.some.inj paired)

theorem sortedStart_bounded (heap after : Mutable.Heap) (closed : Closed heap) (source reverse : Value)
    (reverseInside : reverse.edge.Within heap.length) (items : List Value) (direction : Bool)
    (executed : sortedStart source reverse heap = some (.ok (items, direction), after)) :
    ∀ item ∈ items, item.edge.Within heap.length := by
  obtain ⟨flag, tested⟩ := truth_total heap reverse reverseInside
  cases read : sortedItems source heap with
  | none => simp [sortedStart, Mutable.eval_bind, read] at executed
  | some pair =>
    rcases pair with ⟨outcome, middle⟩
    have same := sortedItems_keeps_heap heap middle source outcome read
    subst middle
    cases outcome with
    | error exception => simp [sortedStart, Mutable.eval_bind, read] at executed
    | ok values =>
      have bounded := sortedItems_bounded heap heap closed source values read
      cases reverse with
      | scalar scalar =>
        simp [sortedStart, Mutable.eval_bind, read, tested] at executed
        rcases executed with ⟨⟨rfl, _⟩, _⟩
        exact bounded
      | ref address =>
        cases found : heap[address]? with
        | none => simp [sortedStart, Mutable.eval_bind, read, tested, found] at executed; rcases executed with ⟨⟨rfl, _⟩, _⟩; exact bounded
        | some object =>
          cases object <;> simp [sortedStart, Mutable.eval_bind, read, tested, found, Mutable.unsupported] at executed
          all_goals rcases executed with ⟨⟨rfl, _⟩, _⟩; exact bounded

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_sortedSource_preserves (value : Value) (parameter : String) (key reverse : Expr)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .sortedSource parameter key reverse env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .sortedSource parameter key reverse env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .sortedSource parameter key reverse env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have captured := inside.2 (.sortedSource parameter key reverse env) (by simp)
  simp only [FrameWithin] at captured
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨captured, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [FrameWithin] using ⟨inside.1, captured⟩
    · exact inside.2 frame (List.mem_cons_of_mem _ member)
  · simp [step, relocateState, relocateWork, relocateFrame, relocateStep]

theorem step_sortedReverse_preserves (value source : Value) (parameter : String) (key : Expr)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .sortedReverse source parameter key env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .sortedReverse source parameter key env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .sortedReverse source parameter key env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have captured := inside.2 (.sortedReverse source parameter key env) (by simp)
  simp only [FrameWithin] at captured
  have stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame :=
    fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)
  have raw := run_readonly_preserves logical physical rename logicalAnchors physicalAnchors
    (sortedStart source value) (sortedStart (relocateValue rename source) (relocateValue rename value))
    (fun pair => (pair.1.map (relocateValue rename), pair.2))
    (fun pair heap => .next ⟨.sortedLoop ⟨parameter, key, env, pair.2⟩ pair.1 [], stack, heap⟩)
    (fun pair heap => .next ⟨.sortedLoop ⟨parameter, key, relocateEnv rename env, pair.2⟩ pair.1 [],
      stack.map (relocateFrame rename), heap⟩)
    globals layout globalsInside
    (fun outcome after executed => sortedStart_keeps_heap logical after source value captured.1 inside.1 outcome executed)
    (sortedStart_relocates logical physical rename layout.runtime source value captured.1 inside.1) (by
      intro pair executed
      apply Preserves.unchanged layout
      · rfl
      · exact ⟨⟨captured.2, sortedStart_bounded logical logical layout.closed source value inside.1 pair.1 pair.2 executed,
          by simp⟩, stackInside⟩
      · rfl)
  simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame] using
    raw.protectGenerator (.sortedReverse source parameter key env :: stack) inside.2

theorem step_sortedKey_preserves (value candidate : Value) (cursor : SequenceSort)
    (remaining : List Value) (keys : List (Value × Value)) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .sortedKey cursor candidate remaining keys :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .sortedKey cursor candidate remaining keys :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .sortedKey cursor candidate remaining keys :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have captured := inside.2 (.sortedKey cursor candidate remaining keys) (by simp)
  simp only [FrameWithin] at captured
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨⟨captured.2.1, captured.2.2.1, ?_⟩, fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)⟩
    intro pair member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨captured.1, inside.1⟩
    · exact captured.2.2.2 pair member
  · simp [step, relocateState, relocateWork, relocateFrame, relocateStep, relocatePair]

theorem step_sorted_key_entry_preserves (cursor : SequenceSort) (candidate : Value)
    (remaining : List Value) (keys : List (Value × Value)) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.sortedLoop cursor (candidate :: remaining) keys, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.sortedLoop cursor (candidate :: remaining) keys, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.sortedLoop cursor (candidate :: remaining) keys, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have candidateInside := inside.1.2.1 candidate (by simp)
  have remainingInside : ∀ value ∈ remaining, value.edge.Within logical.length :=
    fun value member => inside.1.2.1 value (List.mem_cons_of_mem _ member)
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨inside.1.1.setLocal cursor.parameter candidate candidateInside, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [FrameWithin] using ⟨candidateInside, inside.1.1, remainingInside, inside.1.2.2⟩
    · exact inside.2 frame member
  · simp [step, relocateState, relocateWork, relocateFrame, relocateStep, relocateSort, relocateEnv_set]

theorem step_extremumSource_preserves (value : Value) (maximum : Bool) (parameter : String) (key : Expr)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .extremumSource maximum parameter key env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .extremumSource maximum parameter key env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .extremumSource maximum parameter key env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have captured := inside.2 (.extremumSource maximum parameter key env) (by simp)
  simp only [FrameWithin] at captured
  have raw := run_readonly_preserves logical physical rename logicalAnchors physicalAnchors
    (Mutable.sequence value) (Mutable.sequence (relocateValue rename value)) (List.map (relocateValue rename))
    (fun _ heap => .next ⟨.extremumLoop ⟨maximum, value, parameter, key, env⟩ 0 none, stack, heap⟩)
    (fun _ heap => .next ⟨.extremumLoop ⟨maximum, relocateValue rename value, parameter, key, relocateEnv rename env⟩ 0 none,
      stack.map (relocateFrame rename), heap⟩)
    globals layout globalsInside
    (fun outcome after executed => sequence_keeps_heap logical after value outcome executed)
    (layout.runtime.sequence value inside.1) (by
      intro _ _
      apply Preserves.unchanged layout
      · rfl
      · exact ⟨⟨⟨inside.1, captured⟩, by intros; contradiction⟩,
          fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)⟩
      · rfl)
  simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame] using
    raw.protectGenerator (.extremumSource maximum parameter key env :: stack) inside.2

theorem extremumItem_relocates (layout : RuntimeLayout logical physical rename)
    (source : Value) (position : Nat) (inside : source.edge.Within logical.length) :
    extremumItem (relocateValue rename source) position physical =
      (extremumItem source position logical).map
        (fun pair => (pair.1.map (Option.map (relocateValue rename)), physical)) := by
  have paired := layout.sequence source inside
  cases read : Mutable.sequence source logical with
  | none => simp [extremumItem, Mutable.eval_bind, read, paired]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have same := sequence_keeps_heap logical after source outcome read
    subst after
    cases outcome <;> simp [extremumItem, Mutable.eval_bind, read, paired, Except.map, List.getElem?_map]

theorem extremumItem_effect (heap after : Mutable.Heap) (closed : Closed heap)
    (source : Value) (position : Nat) (outcome : Except ExceptionObject (Option Value))
    (executed : extremumItem source position heap = some (outcome, after)) :
    after = heap ∧ ∀ value, outcome = .ok (some value) → value.edge.Within heap.length := by
  cases read : Mutable.sequence source heap with
  | none => simp [extremumItem, Mutable.eval_bind, read] at executed
  | some pair =>
    rcases pair with ⟨result, middle⟩
    have same := sequence_keeps_heap heap middle source result read
    subst middle
    cases result with
    | error exception =>
      simp [extremumItem, Mutable.eval_bind, read] at executed
      rcases executed with ⟨rfl, rfl⟩
      exact ⟨rfl, by intros; contradiction⟩
    | ok items =>
      simp [extremumItem, Mutable.eval_bind, read] at executed
      rcases executed with ⟨rfl, rfl⟩
      refine ⟨rfl, ?_⟩
      intro value equal
      have found : items[position]? = some value := Except.ok.inj equal
      exact sequence_items_within heap heap closed source items read value (List.mem_of_getElem? found)

theorem step_extremum_loop_preserves (cursor : SequenceExtremum) (position : Nat)
    (best : Option (Value × Value)) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.extremumLoop cursor position best, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.extremumLoop cursor position best, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.extremumLoop cursor position best, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  let next := fun (cursor : SequenceExtremum) (best : Option (Value × Value))
      (stack : List Frame) (anchors : Nat) (globals : Mutable.Globals) (item : Option Value) (heap : Mutable.Heap) =>
    match item with
    | none => match best with
      | none => done anchors heap (.error ⟨"ValueError", []⟩) globals
      | some (winner, _) => .next ⟨.value winner, stack, heap⟩
    | some candidate => .next ⟨.expr cursor.key (setLocal cursor.env cursor.parameter candidate),
        .extremumKey cursor position candidate best :: stack, heap⟩
  have raw := run_readonly_preserves logical physical rename logicalAnchors physicalAnchors
    (extremumItem cursor.source position) (extremumItem (relocateValue rename cursor.source) position)
    (Option.map (relocateValue rename))
    (next cursor best stack logicalAnchors globals)
    (next (relocateExtremum rename cursor) (best.map (relocatePair rename)) (stack.map (relocateFrame rename))
      physicalAnchors (relocateGlobals rename globals))
    globals layout globalsInside
    (fun outcome after executed => (extremumItem_effect logical after layout.closed cursor.source position outcome executed).1)
    (extremumItem_relocates logical physical rename layout.runtime cursor.source position inside.1.1.1) (by
      intro item executed
      apply Preserves.unchanged layout
      · cases item with
        | none => cases best <;> rfl
        | some candidate => rfl
      · cases item with
        | none =>
          cases found : best with
          | none => exact ⟨globalsInside, by intros; contradiction⟩
          | some pair => exact ⟨(inside.1.2 pair found).1, inside.2⟩
        | some candidate =>
          have bounded := (extremumItem_effect logical logical layout.closed cursor.source position _ executed).2 candidate rfl
          refine ⟨inside.1.1.2.setLocal cursor.parameter candidate bounded, ?_⟩
          intro frame member
          rcases List.mem_cons.mp member with rfl | member
          · simpa only [FrameWithin] using ⟨bounded, inside.1.1, inside.1.2⟩
          · exact inside.2 frame member
      · cases item with
        | none => cases best <;> rfl
        | some candidate => simp [next, relocateStep, relocateState, relocateWork, relocateFrame,
            relocateExtremum, relocateEnv_set])
  simpa only [step, relocateState, relocateWork, relocateExtremum, next] using raw.protectGenerator stack inside.2

/-- Key preparation excludes final sorting and comparison of a candidate with an existing winner. -/
inductive KeyPreparation : Work → List Frame → Prop where
  | source (value : Value) (parameter : String) (key reverse : Expr) (env : Env) (stack : List Frame) :
      KeyPreparation (.value value) (.sortedSource parameter key reverse env :: stack)
  | reverse (value source : Value) (parameter : String) (key : Expr) (env : Env) (stack : List Frame) :
      KeyPreparation (.value value) (.sortedReverse source parameter key env :: stack)
  | key (value candidate : Value) (cursor : SequenceSort) (remaining : List Value)
      (keys : List (Value × Value)) (stack : List Frame) :
      KeyPreparation (.value value) (.sortedKey cursor candidate remaining keys :: stack)
  | sorting (cursor : SequenceSort) (candidate : Value) (remaining : List Value)
      (keys : List (Value × Value)) (stack : List Frame) :
      KeyPreparation (.sortedLoop cursor (candidate :: remaining) keys) stack
  | extremumSource (value : Value) (maximum : Bool) (parameter : String) (key : Expr) (env : Env) (stack : List Frame) :
      KeyPreparation (.value value) (.extremumSource maximum parameter key env :: stack)
  | extremum (cursor : SequenceExtremum) (position : Nat) (best : Option (Value × Value)) (stack : List Frame) :
      KeyPreparation (.extremumLoop cursor position best) stack

theorem step_keyPreparation_preserves (work : Work) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename) (preparation : KeyPreparation work stack)
    (inside : StateWithin ⟨work, stack, logical⟩) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨work, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨work, stack, logical⟩) (relocateGlobals rename globals)) := by
  cases preparation with
  | source => apply step_sortedSource_preserves <;> assumption
  | reverse => apply step_sortedReverse_preserves <;> assumption
  | key => apply step_sortedKey_preserves <;> assumption
  | sorting => apply step_sorted_key_entry_preserves <;> assumption
  | extremumSource => apply step_extremumSource_preserves <;> assumption
  | extremum => apply step_extremum_loop_preserves <;> assumption

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_keyPreparation_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (work : HeapCalls.Work) (stack : List HeapCalls.Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module)
    (layout : ExecutionLayout logical physical rename) (preparation : KeyPreparation work stack)
    (inside : StateWithin logical.length (.running ⟨⟨work, stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running ⟨⟨work, stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running ⟨⟨work, stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running ⟨⟨work, stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_keyPreparation_preserves module logical physical rename logicalAnchors physicalAnchors
      work stack globals layout preparation ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
