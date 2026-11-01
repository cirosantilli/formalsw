import lang.py.FormalSW.MachineSequenceOperationInvariant

/-! Shared first-iterator acquisition for immediately consumed generators. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

inductive GeneratorSource where
  | sequence | range | enumerate | zip | permutations | combinations

/-- Only next's acquisition recognizes combinations and excludes unknown sequence protocols. -/
def generatorSource (nextOnly : Bool) : Expr → GeneratorSource
  | .permutationsIterable _ => .permutations
  | .combinationsIterable _ => if nextOnly then .combinations else .sequence
  | .zipIterable _ => .zip
  | .call (.name "enumerate") _ => .enumerate
  | .call (.name "range") _ => .range
  | _ => .sequence

def generatorSequence (nextOnly : Bool) (source : Value) : Mutable.Eval (List Value) :=
  if nextOnly then nextSequence source else Mutable.sequence source

/-- A proof-level normalization; the interpreter continues to execute its original definitions. -/
def generatorAcquire (anchors : Nat) (kind : GeneratorSource) (nextOnly : Bool) (target : Expr)
    (body : List Stmt) (values : List Value) (heap : Mutable.Heap) (globals : Mutable.Globals)
    (enter : Stmt → Mutable.Heap → Step State Mutable.Completion) : Step State Mutable.Completion :=
  let name := comprehensionTargetName target
  let wrapped := comprehensionTargetBody target body
  match kind with
  | .permutations => run anchors heap (permutationRows values)
      (fun rows heap => enter (.permutationStepLoop name rows wrapped []) heap) globals
  | .combinations => run anchors heap (combinationRows values)
      (fun rows heap => enter (.permutationStepLoop name rows wrapped []) heap) globals
  | .zip => run anchors heap (zipSources values)
      (fun sources heap => enter (.zipStepLoop name sources 0 wrapped []) heap) globals
  | .enumerate => match enumerateTarget target, values with
      | some (index, name), [source, start] =>
          run anchors heap (enumerateStart start) (fun counter heap =>
            run anchors heap (generatorSequence nextOnly source)
              (fun _ heap => enter (.enumerateStepLoop index name (sequenceSource source) 0 counter body []) heap)
              globals) globals
      | _, _ => .unsupported
  | .range => match rangeBounds values with
      | .ok (first, stop, stride) => enter (.rangeStepLoop name first stop stride wrapped []) heap
      | .error exception => done anchors heap (.error exception) globals
  | .sequence => match values with
      | [source] => run anchors heap (generatorSequence nextOnly source)
          (fun _ heap => enter (.sequenceStepLoop name (sequenceSource source) 0 wrapped []) heap) globals
      | _ => .unsupported

theorem nextSequence_positionalPool (source : Value) : nextSequence source = positionalPool source := by
  funext heap
  cases source with
  | scalar scalar => rfl
  | ref address =>
    cases found : heap[address]? with
    | none => simp [nextSequence, positionalPool, found, Mutable.sequence, Mutable.unsupported]
    | some object => cases object <;> simp [nextSequence, positionalPool, found, Mutable.unsupported]

theorem generatorSequence_keeps_heap (nextOnly : Bool) (heap after : Mutable.Heap) (source : Value)
    (outcome : Except ExceptionObject (List Value))
    (executed : generatorSequence nextOnly source heap = some (outcome, after)) : after = heap := by
  cases nextOnly with
  | false => exact sequence_keeps_heap heap after source outcome executed
  | true =>
    exact positionalPool_keeps_heap heap source outcome after
      (by simpa only [generatorSequence, if_true, nextSequence_positionalPool] using executed)

theorem generatorSequence_relocates (nextOnly : Bool) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (source : Value) (inside : source.edge.Within logical.length) :
    generatorSequence nextOnly (relocateValue rename source) physical =
      (generatorSequence nextOnly source logical).map (fun pair => (pair.1.map (List.map (relocateValue rename)), physical)) := by
  cases nextOnly with
  | false => exact layout.sequence source inside
  | true => simpa only [generatorSequence, if_true, nextSequence_positionalPool] using positionalPool_relocates layout source inside

theorem generatorAcquire_preserves (kind : GeneratorSource) (nextOnly : Bool) (target : Expr)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (body : List Stmt) (values : List Value) (globals : Mutable.Globals)
    (enter otherEnter : Stmt → Mutable.Heap → Step State Mutable.Completion)
    (layout : ExecutionLayout logical physical rename)
    (bodyInside : ∀ statement ∈ body, StmtWithin logical.length statement)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (globalsInside : GlobalsWithin logical.length globals)
    (continues : ∀ loop, StmtWithin logical.length loop →
      Preserves logical physical rename physicalAnchors (enter loop logical) (otherEnter (relocateStmt rename loop) physical)) :
    Preserves logical physical rename physicalAnchors
      (generatorAcquire logicalAnchors kind nextOnly target body values logical globals enter)
      (generatorAcquire physicalAnchors kind nextOnly target (body.map (relocateStmt rename))
        (values.map (relocateValue rename)) physical (relocateGlobals rename globals) otherEnter) := by
  have wrappedInside := comprehensionTargetBody_within logical.length target body bodyInside
  cases kind with
  | permutations =>
    apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _
      (List.map (List.map (relocateSource rename))) _ _ globals layout globalsInside
      (fun outcome after executed => permutationRows_keeps_heap logical values outcome after executed)
      (permutationRows_relocates layout.runtime values valuesInside)
    intro rows captured
    simpa only [relocateStmt, comprehensionTargetBody_relocates, List.map_nil] using
      continues (.permutationStepLoop (comprehensionTargetName target) rows (comprehensionTargetBody target body) [])
        (by simp only [StmtWithin]; exact ⟨permutationRows_within logical layout.closed values rows captured, wrappedInside, by simp⟩)
  | combinations =>
    apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _
      (List.map (List.map (relocateSource rename))) _ _ globals layout globalsInside
      (fun outcome after executed => combinationRows_keeps_heap logical values outcome after executed)
      (combinationRows_relocates layout.runtime values valuesInside)
    intro rows captured
    simpa only [relocateStmt, comprehensionTargetBody_relocates, List.map_nil] using
      continues (.permutationStepLoop (comprehensionTargetName target) rows (comprehensionTargetBody target body) [])
        (by simp only [StmtWithin]; exact ⟨combinationRows_within logical layout.closed values rows captured, wrappedInside, by simp⟩)
  | zip =>
    apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _
      (List.map (relocateSource rename)) _ _ globals layout globalsInside
      (fun outcome after executed => zipSources_keeps_heap logical values outcome after executed)
      (zipSources_relocates layout.runtime values valuesInside)
    intro sources captured
    have sourcesInside : ∀ source ∈ sources, SourceWithin logical.length source := by
      rw [zipSources_captured logical values sources captured]
      intro source member
      obtain ⟨value, present, rfl⟩ := List.mem_map.mp member
      exact sequenceSource_within logical.length value (valuesInside value present)
    simpa only [relocateStmt, comprehensionTargetBody_relocates, List.map_nil] using
      continues (.zipStepLoop (comprehensionTargetName target) sources 0 (comprehensionTargetBody target body) [])
        (by simp only [StmtWithin]; exact ⟨sourcesInside, wrappedInside, by simp⟩)
  | range =>
    simp only [generatorAcquire, rangeBounds_relocate]
    cases tested : rangeBounds values with
    | error exception =>
      exact Preserves.unchanged layout rfl ⟨globalsInside, by intro value impossible; cases impossible⟩ rfl
    | ok bounds =>
      rcases bounds with ⟨first, stop, stride⟩
      simpa only [relocateStmt, comprehensionTargetBody_relocates, List.map_nil] using
        continues (.rangeStepLoop (comprehensionTargetName target) first stop stride (comprehensionTargetBody target body) [])
          (by simp only [StmtWithin]; exact ⟨wrappedInside, by simp⟩)
  | sequence =>
    rcases values with _ | ⟨source, _ | ⟨extra, rest⟩⟩
    case nil => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
    case cons.cons => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
    have sourceInside := valuesInside source (by simp)
    simp only [generatorAcquire, List.map_cons, List.map_nil]
    apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _
      (List.map (relocateValue rename)) _ _ globals layout globalsInside
      (fun outcome after executed => generatorSequence_keeps_heap nextOnly logical after source outcome executed)
      (generatorSequence_relocates nextOnly logical physical rename layout.runtime source sourceInside)
    intro items captured
    simpa only [relocateStmt, sequenceSource_relocate, comprehensionTargetBody_relocates, List.map_nil] using
      continues (.sequenceStepLoop (comprehensionTargetName target) (sequenceSource source) 0 (comprehensionTargetBody target body) [])
        (by simp only [StmtWithin]; exact ⟨sequenceSource_within logical.length source sourceInside, wrappedInside, by simp⟩)
  | enumerate =>
    cases selected : enumerateTarget target with
    | none =>
      exact Preserves.unchanged layout (by simp [generatorAcquire, selected, StepHeap])
        (by simp [generatorAcquire, selected, StepWithin]) (by simp [generatorAcquire, selected, relocateStep])
    | some names =>
      rcases names with ⟨index, name⟩
      rcases values with _ | ⟨source, _ | ⟨start, _ | ⟨extra, rest⟩⟩⟩
      case nil =>
        exact Preserves.unchanged layout (by simp [generatorAcquire, selected, StepHeap])
          (by simp [generatorAcquire, selected, StepWithin]) (by simp [generatorAcquire, selected, relocateStep])
      case cons.nil =>
        exact Preserves.unchanged layout (by simp [generatorAcquire, selected, StepHeap])
          (by simp [generatorAcquire, selected, StepWithin]) (by simp [generatorAcquire, selected, relocateStep])
      case cons.cons.cons =>
        exact Preserves.unchanged layout (by simp [generatorAcquire, selected, StepHeap])
          (by simp [generatorAcquire, selected, StepWithin]) (by simp [generatorAcquire, selected, relocateStep])
      have sourceInside := valuesInside source (by simp)
      simp only [generatorAcquire, selected, List.map_cons, List.map_nil]
      apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ id _ _ globals layout globalsInside
        (by
          intro outcome after executed
          obtain ⟨result, evaluated⟩ := enumerateStart_total logical start
          rw [evaluated] at executed
          exact (Prod.mk.inj (Option.some.inj executed)).2.symm)
        (by simpa only [Except.map_id] using enumerateStart_relocate logical physical rename start)
      intro counter tested
      apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _
        (List.map (relocateValue rename)) _ _ globals layout globalsInside
        (fun outcome after executed => generatorSequence_keeps_heap nextOnly logical after source outcome executed)
        (generatorSequence_relocates nextOnly logical physical rename layout.runtime source sourceInside)
      intro items captured
      simpa only [relocateStmt, sequenceSource_relocate, List.map_nil, id_eq] using
        continues (.enumerateStepLoop index name (sequenceSource source) 0 counter body [])
          (by simp only [StmtWithin]; exact ⟨sequenceSource_within logical.length source sourceInside, bodyInside, by simp⟩)

end FormalSW.PyAst.HeapCalls.Relocation
