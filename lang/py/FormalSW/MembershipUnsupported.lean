import lang.py.FormalSW.MembershipDispatchRelocation
import lang.py.FormalSW.ComparisonUnsupported

/-! Membership preserves unsupported outcomes without inspecting a skipped search tail. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

/-- Only comparisons reached by the search need to avoid recursive sequence traversal. -/
def NonrecursiveSearch (heap : Heap) (needle : Value) : List Value → Prop
  | [] => True
  | item :: rest => if item = needle then True else
      NonrecursiveComparison heap .eq item needle ∧
      (HeapCalls.compare .eq item needle heap = some (.ok (.scalar (.bool false)), heap) →
        NonrecursiveSearch heap needle rest)

def NonrecursiveMembership (heap : Heap) (needle container : Value) : Prop :=
  match container with
  | .ref address => match heap[address]? with
      | some (.list items) | some (.tuple items) => NonrecursiveSearch heap needle items
      | _ => True
  | .scalar _ => True

theorem NonrecursiveSearch.of_comparisons (heap : Heap) (needle : Value) (items : List Value)
    (comparisons : ∀ item ∈ items, NonrecursiveComparison heap .eq item needle) :
    NonrecursiveSearch heap needle items := by
  induction items with
  | nil => trivial
  | cons item rest ih =>
    unfold NonrecursiveSearch
    split
    · trivial
    · exact ⟨comparisons item (by simp), fun _ => ih (fun value member => comparisons value (by simp [member]))⟩

theorem NonrecursiveSearch.scalar (heap : Heap) (needle : Constant) (items : List Value) :
    NonrecursiveSearch heap (.scalar needle) items := by
  apply NonrecursiveSearch.of_comparisons
  intro item _
  cases item <;> trivial

theorem NonrecursiveMembership.scalar (heap : Heap) (needle : Constant) (container : Value) :
    NonrecursiveMembership heap (.scalar needle) container := by
  cases container with
  | scalar scalar => trivial
  | ref address =>
    cases found : heap[address]? with
    | none => simp [NonrecursiveMembership, found]
    | some object =>
      cases object <;> simp only [NonrecursiveMembership, found]
      all_goals first | trivial | exact NonrecursiveSearch.scalar heap needle _

theorem RuntimeLayout.sequenceContains_nonrecursive {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (needle : Value) (items : List Value) (needleInside : needle.edge.Within logical.length)
    (itemsInside : ∀ item ∈ items, item.edge.Within logical.length)
    (nonrecursive : NonrecursiveSearch logical needle items) :
    HeapCalls.sequenceContains (relocateValue rename needle) (items.map (relocateValue rename)) physical =
      (HeapCalls.sequenceContains needle items logical).map (fun pair => (pair.1, physical)) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    have headInside := itemsInside item (by simp)
    have tailInside : ∀ value ∈ rest, value.edge.Within logical.length :=
      fun value member => itemsInside value (by simp [member])
    have identity := relocateValue_eq_iff logical.length rename layout.injective item needle headInside needleInside
    by_cases same : item = needle
    · simp [HeapCalls.sequenceContains, same]
    · have different : relocateValue rename item ≠ relocateValue rename needle := fun equal => same (identity.mp equal)
      simp only [NonrecursiveSearch, same, if_false] at nonrecursive
      have other := layout.compare_nonrecursive closed .eq item needle headInside needleInside nonrecursive.1
      cases compared : HeapCalls.compare .eq item needle logical with
      | none => simp [HeapCalls.sequenceContains, same, different, other, compared, eval_bind]
      | some pair =>
        rcases pair with ⟨comparison, middle⟩
        obtain ⟨answer, resultSame, unchanged⟩ := compare_effect logical middle .eq item needle
          headInside needleInside comparison compared
        subst middle
        rw [resultSame] at compared
        rw [compared] at other
        cases answer with
        | error exception =>
          simp only [Option.map_some, Except.map] at compared other
          simp [HeapCalls.sequenceContains, same, different, other, compared, eval_bind]
        | ok answer =>
          simp only [Option.map_some, Except.map] at compared other
          change HeapCalls.compare .eq (relocateValue rename item) (relocateValue rename needle) physical =
            some (.ok (.scalar (.bool answer)), physical) at other
          cases answer with
          | true => simp [HeapCalls.sequenceContains, same, different, other, compared, eval_bind, Mutable.truth, scalarTruth]
          | false =>
            have tail := ih tailInside (nonrecursive.2 compared)
            simpa [HeapCalls.sequenceContains, same, different, other, compared, eval_bind, Mutable.truth, scalarTruth] using tail

theorem RuntimeLayout.membership_sequences_nonrecursive {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (isTuple : Bool) (needle : Value) (address : Nat) (items : List Value) (negated : Bool)
    (found : logical[address]? = some (comparisonObject isTuple items))
    (needleInside : needle.edge.Within logical.length) (nonrecursive : NonrecursiveSearch logical needle items) :
    HeapCalls.membership (relocateValue rename needle) (.ref (rename address)) negated physical =
      (HeapCalls.membership needle (.ref address) negated logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  have moved := layout.lookup address _ found
  rw [comparisonObject_relocates] at moved
  have inside : ∀ value ∈ items, value.edge.Within logical.length := by
    have bounded := closed _ (List.mem_of_getElem? found)
    cases isTuple <;> exact bounded
  rw [membership_sequence_eq logical isTuple needle address items negated found,
    membership_sequence_eq physical isTuple (relocateValue rename needle) (rename address) _ negated moved,
    layout.sequenceContains_nonrecursive closed needle items needleInside inside nonrecursive]
  simp only [Option.map_map, Function.comp_def]
  congr 1
  funext pair
  rcases pair with ⟨outcome, after⟩
  cases outcome <;> rfl

theorem RuntimeLayout.membership_nonrecursive {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (needle container : Value) (negated : Bool)
    (needleInside : needle.edge.Within logical.length) (containerInside : container.edge.Within logical.length)
    (nonrecursive : NonrecursiveMembership logical needle container) :
    HeapCalls.membership (relocateValue rename needle) (relocateValue rename container) negated physical =
      (HeapCalls.membership needle container negated logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  cases container with
  | scalar scalar => exact layout.membership_scalar needle scalar negated needleInside
  | ref address =>
    have found := List.getElem?_eq_getElem containerInside
    generalize objectValue : logical[address] = object at found
    have moved := layout.lookup address _ found
    cases object with
    | list items =>
      apply layout.membership_sequences_nonrecursive closed false needle address items negated found needleInside
      simpa [NonrecursiveMembership, found] using nonrecursive
    | tuple items =>
      apply layout.membership_sequences_nonrecursive closed true needle address items negated found needleInside
      simpa [NonrecursiveMembership, found] using nonrecursive
    | bytearray bytes => exact layout.membership_bytearray needle address bytes negated found needleInside
    | set items => exact layout.membership_set closed address items needle negated found needleInside
    | keySet items => exact layout.membership_keySet closed address items needle negated found needleInside
    | dict entries => exact layout.membership_dict closed address entries needle negated found needleInside
    | keyDict entries => exact layout.membership_keyDict closed address entries needle negated found needleInside
    | «instance» origin name fields | dataInstance origin name frozen declared fields =>
      simp [HeapCalls.membership, relocateValue, found, moved, relocateObject, unsupported]

end FormalSW.PyAst.Mutable.Relocation
