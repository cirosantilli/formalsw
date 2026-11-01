import lang.py.FormalSW.MachineGeneratorAcquisition
import lang.py.FormalSW.MachineDictionaryIteration

/-! Acquiring an items generator retains live keys and validates custom dispatch before the sum start. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- The receiver is read once; acquisition neither copies the dictionary nor changes its heap. -/
theorem dictionaryItemsSumStart_preserves (element target iterable : Expr) (filters : List Expr)
    (rest : List (Expr × Expr × List Expr)) (start : Expr)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (env : Env) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (envInside : EnvWithin logical.length env)
    (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (dictionaryItemsSumStart logicalAnchors element target iterable filters rest env start values stack logical globals)
      (dictionaryItemsSumStart physicalAnchors element target iterable filters rest (relocateEnv rename env) start
        (values.map (relocateValue rename)) (stack.map (relocateFrame rename)) physical (relocateGlobals rename globals)) := by
  rcases values with _ | ⟨receiver, _ | ⟨extra, tail⟩⟩
  case nil => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  case cons.cons => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  have receiverInside := valuesInside receiver (by simp)
  let body := comprehensionTargetBody target
    (comprehensionFilters filters (comprehensionTargetsBody (sumBody element []) rest))
  have bodySource : ∀ statement ∈ body, StmtWithin 0 statement :=
    comprehensionTargetBody_within 0 target _
      (SetCalls.Relocation.comprehensionFilters_within 0 filters _
        (SetCalls.Relocation.comprehensionTargetsBody_within 0 _ rest (SetCalls.Relocation.sumBody_source element [])))
  cases receiver with
  | scalar value =>
    exact Preserves.unchanged layout rfl ⟨globalsInside, by intro value impossible; cases impossible⟩ rfl
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem receiverInside
    have moved := layout.runtime.lookup address _ found
    cases fields : dictionaryItemFields logical[address] with
    | some entries =>
      have bounded := dictionaryItemFields_within logical.length logical[address] entries
        (layout.closed logical[address] (List.mem_of_getElem? found)) fields
      simp only [List.map_cons, List.map_nil, relocateValue, dictionaryItemsSumStart, found, moved,
        dictionaryItemFields_relocates, fields, Option.map_some]
      apply Preserves.unchanged layout
      · rfl
      · refine ⟨envInside, ?_⟩
        intro frame member
        rcases List.mem_cons.mp member with rfl | member
        · simp only [FrameWithin, StmtWithin]
          refine ⟨SetCalls.Relocation.comprehensionTargetsEnv_within logical.length env _ envInside,
            receiverInside, ?_, ?_, by simp⟩
          · intro key present
            obtain ⟨entry, member, rfl⟩ := List.mem_map.mp present
            exact sequenceSource_within logical.length entry.1 (bounded entry member).1
          · exact fun statement present => (bodySource statement present).mono (Nat.zero_le _)
        · exact stackInside frame member
      · simp only [relocateStep, relocateState, relocateWork, List.map_cons, List.map_nil, relocateFrame,
          relocateStmt, dictionaryKeys_relocate, SetCalls.Relocation.comprehensionTargetsEnv_relocates]
        rw [relocateBody_source rename body bodySource]
    | none =>
      cases object : logical[address] <;> simp only [object, relocateObject] at moved
      all_goals simp only [object, dictionaryItemFields] at fields
      all_goals try contradiction
      all_goals simp only [List.map_cons, List.map_nil, relocateValue, dictionaryItemsSumStart,
        found, object, moved, dictionaryItemFields]
      case «instance» origin className attributes =>
        apply Preserves.unchanged layout
        · rfl
        · refine ⟨receiverInside, ?_⟩
          intro frame member
          rcases List.mem_cons.mp member with rfl | member
          · simpa only [FrameWithin] using envInside
          rcases List.mem_cons.mp member with rfl | member
          · simpa [FrameWithin, OperationWithin] using envInside
          · exact stackInside frame member
        · simp [relocateStep, relocateState, relocateWork, relocateFrame, relocateRuntimeOperation, relocateOperation, relocateValue]
      case dataInstance origin className frozen declared attributes =>
        apply Preserves.unchanged layout
        · rfl
        · refine ⟨receiverInside, ?_⟩
          intro frame member
          rcases List.mem_cons.mp member with rfl | member
          · simpa only [FrameWithin] using envInside
          rcases List.mem_cons.mp member with rfl | member
          · simpa [FrameWithin, OperationWithin] using envInside
          · exact stackInside frame member
        · simp [relocateStep, relocateState, relocateWork, relocateFrame, relocateRuntimeOperation, relocateOperation, relocateValue]
      all_goals exact Preserves.unchanged layout rfl ⟨globalsInside, by intro value impossible; cases impossible⟩ rfl

end FormalSW.PyAst.HeapCalls.Relocation
