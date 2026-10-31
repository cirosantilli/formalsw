import lang.py.FormalSW.ComparisonDispatchRelocation

/-! Sequence membership preserves identity shortcuts, equality order, and exception exits. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

theorem relocateValue_eq_iff (limit : Nat) (rename : Nat → Nat)
    (injective : Graph.Relocation.InjectiveBelow rename limit) (left right : Value)
    (leftInside : left.edge.Within limit) (rightInside : right.edge.Within limit) :
    relocateValue rename left = relocateValue rename right ↔ left = right := by
  cases left with
  | scalar scalar => cases right <;> simp [relocateValue]
  | ref address =>
    cases right with
    | scalar scalar => simp [relocateValue]
    | ref other =>
      simp only [relocateValue, Value.ref.injEq]
      exact ⟨injective address leftInside other rightInside, congrArg rename⟩

/-- An unsupported comparison cannot be skipped; a successful earlier match skips the remaining tail. -/
theorem RuntimeLayout.sequenceContains {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (needle : Value) (items : List Value) (needleInside : needle.edge.Within logical.length)
    (itemsInside : ∀ item ∈ items, item.edge.Within logical.length)
    (outcome : Except ExceptionObject Bool) (after : Heap)
    (executed : HeapCalls.sequenceContains needle items logical = some (outcome, after)) :
    after = logical ∧ HeapCalls.sequenceContains (relocateValue rename needle)
      (items.map (relocateValue rename)) physical = some (outcome, physical) := by
  induction items generalizing outcome after with
  | nil =>
    have same : .ok false = outcome ∧ logical = after := by simpa [HeapCalls.sequenceContains] using executed
    rw [← same.1]
    exact ⟨same.2.symm, rfl⟩
  | cons item rest ih =>
    have headInside := itemsInside item (by simp)
    have tailInside : ∀ value ∈ rest, value.edge.Within logical.length :=
      fun value member => itemsInside value (by simp [member])
    have identity := relocateValue_eq_iff logical.length rename layout.injective item needle headInside needleInside
    by_cases same : item = needle
    · have result : .ok true = outcome ∧ logical = after := by
        simpa [HeapCalls.sequenceContains, same] using executed
      refine ⟨result.2.symm, ?_⟩
      rw [← result.1]
      simp [HeapCalls.sequenceContains, same]
    · have different : relocateValue rename item ≠ relocateValue rename needle :=
        fun equal => same (identity.mp equal)
      cases compared : HeapCalls.compare .eq item needle logical with
      | none => simp [HeapCalls.sequenceContains, same, compared, eval_bind] at executed
      | some pair =>
        rcases pair with ⟨comparison, middle⟩
        obtain ⟨result, resultSame, unchanged⟩ := compare_effect logical middle .eq item needle
          headInside needleInside comparison compared
        subst middle
        rw [resultSame] at compared
        have other := layout.compare closed .eq item needle headInside needleInside _ _ compared
        cases result with
        | error exception =>
          simp only [Except.map] at compared other
          have failure : .error exception = outcome ∧ logical = after := by
            simpa [HeapCalls.sequenceContains, same, compared, eval_bind] using executed
          refine ⟨failure.2.symm, ?_⟩
          rw [← failure.1]
          simp [HeapCalls.sequenceContains, different, other, eval_bind]
        | ok answer =>
          simp only [Except.map] at compared other
          change HeapCalls.compare .eq (relocateValue rename item) (relocateValue rename needle) physical =
            some (.ok (.scalar (.bool answer)), physical) at other
          cases answer with
          | true =>
            have success : .ok true = outcome ∧ logical = after := by
              simpa [HeapCalls.sequenceContains, same, compared, eval_bind, Mutable.truth, scalarTruth] using executed
            refine ⟨success.2.symm, ?_⟩
            rw [← success.1]
            simp [HeapCalls.sequenceContains, different, other, eval_bind, Mutable.truth, scalarTruth]
          | false =>
            have remaining : HeapCalls.sequenceContains needle rest logical = some (outcome, after) := by
              simpa [HeapCalls.sequenceContains, same, compared, eval_bind, Mutable.truth, scalarTruth] using executed
            obtain ⟨unchanged, transported⟩ := ih tailInside outcome after remaining
            refine ⟨unchanged, ?_⟩
            simpa [HeapCalls.sequenceContains, different, other, eval_bind, Mutable.truth, scalarTruth] using transported

theorem ExecutionLayout.sequenceContains {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (needle : Value) (items : List Value)
    (needleInside : needle.edge.Within logical.length)
    (itemsInside : ∀ item ∈ items, item.edge.Within logical.length)
    (outcome : Except ExceptionObject Bool) (after : Heap)
    (executed : HeapCalls.sequenceContains needle items logical = some (outcome, after)) :
    HeapCalls.sequenceContains (relocateValue rename needle) (items.map (relocateValue rename)) physical =
        some (outcome, physical) ∧ ExecutionLayout after physical rename := by
  obtain ⟨unchanged, transported⟩ := layout.runtime.sequenceContains layout.closed needle items needleInside itemsInside _ _ executed
  exact ⟨transported, unchanged ▸ layout⟩

theorem membership_sequence_eq (heap : Heap) (isTuple : Bool) (needle : Value) (address : Nat)
    (items : List Value) (negated : Bool) (found : heap[address]? = some (comparisonObject isTuple items)) :
    HeapCalls.membership needle (.ref address) negated heap =
      (HeapCalls.sequenceContains needle items heap).map (fun pair =>
        (pair.1.map (fun answer => Value.scalar (.bool (if negated then !answer else answer))), pair.2)) := by
  cases searched : HeapCalls.sequenceContains needle items heap with
  | none => cases isTuple <;> simp [HeapCalls.membership, comparisonObject, found, searched, eval_bind]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    cases outcome <;> cases isTuple <;>
      simp [HeapCalls.membership, comparisonObject, found, searched, eval_bind, Except.map]

theorem RuntimeLayout.membership_sequences {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (isTuple : Bool) (needle : Value) (address : Nat) (items : List Value) (negated : Bool)
    (found : logical[address]? = some (comparisonObject isTuple items))
    (needleInside : needle.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : HeapCalls.membership needle (.ref address) negated logical = some (outcome, after)) :
    after = logical ∧ HeapCalls.membership (relocateValue rename needle) (.ref (rename address)) negated physical =
      some (outcome.map (relocateValue rename), physical) := by
  have moved := layout.lookup address _ found
  rw [comparisonObject_relocates] at moved
  have inside : ∀ value ∈ items, value.edge.Within logical.length := by
    have bounded := closed _ (List.mem_of_getElem? found)
    cases isTuple <;> exact bounded
  rw [membership_sequence_eq logical isTuple needle address items negated found] at executed
  cases searched : HeapCalls.sequenceContains needle items logical with
  | none => simp [searched] at executed
  | some pair =>
    rcases pair with ⟨result, middle⟩
    have preserved := layout.sequenceContains closed needle items needleInside inside result middle searched
    simp only [searched, Option.map_some, Option.some.injEq, Prod.mk.injEq] at executed
    refine ⟨executed.2.symm.trans preserved.1, ?_⟩
    rw [membership_sequence_eq physical isTuple (relocateValue rename needle) (rename address) _ negated moved,
      preserved.2, ← executed.1]
    cases result <;> rfl

theorem ExecutionLayout.membership_sequences {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (isTuple : Bool) (needle : Value)
    (address : Nat) (items : List Value) (negated : Bool)
    (found : logical[address]? = some (comparisonObject isTuple items))
    (needleInside : needle.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : HeapCalls.membership needle (.ref address) negated logical = some (outcome, after)) :
    HeapCalls.membership (relocateValue rename needle) (.ref (rename address)) negated physical =
        some (outcome.map (relocateValue rename), physical) ∧ ExecutionLayout after physical rename := by
  obtain ⟨unchanged, transported⟩ := layout.runtime.membership_sequences layout.closed isTuple needle address items
    negated found needleInside outcome after executed
  exact ⟨transported, unchanged ▸ layout⟩

end FormalSW.PyAst.Mutable.Relocation
