import lang.py.FormalSW.DataRuntime

namespace FormalSW.PyAst

namespace Execution

/-- Change the relation on successful results while still matching exceptions
and termination in both directions. The results may include observable state. -/
def OutcomeRelated (relation : α → β → Prop) : Except ExceptionObject α →
    Except ExceptionObject β → Prop
  | .ok a, .ok b => relation a b
  | .error a, .error b => a = b
  | _, _ => False

def EquivBy (relation : α → β → Prop) (left : Execution α) (right : Execution β) : Prop :=
  (∀ a, Finishes left.step left.initial a →
    ∃ b, Finishes right.step right.initial b ∧ OutcomeRelated relation a b) ∧
  (∀ b, Finishes right.step right.initial b →
    ∃ a, Finishes left.step left.initial a ∧ OutcomeRelated relation a b)

theorem EquivBy.returns_iff {left : Execution α} {right : Execution β}
    (h : EquivBy relation left right) : left.Returns ↔ right.Returns := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb, hr⟩ := h.1 _ ha
    cases b with
    | ok b => exact ⟨b, hb⟩
    | error _ => exact False.elim hr
  · rintro ⟨b, hb⟩
    obtain ⟨a, ha, hr⟩ := h.2 _ hb
    cases a with
    | ok a => exact ⟨a, ha⟩
    | error _ => exact False.elim hr

theorem EquivBy.halts_iff {left : Execution α} {right : Execution β}
    (h : EquivBy relation left right) : left.Halts ↔ right.Halts := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb, _⟩ := h.1 _ ha
    exact ⟨b, hb⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, ha, _⟩ := h.2 _ hb
    exact ⟨a, ha⟩

/-- Existing exact-result equivalence is the equality instance of EquivBy. -/
theorem equivBy_eq_iff (left right : Execution α) : EquivBy Eq left right ↔ left.Equiv right := by
  have same : ∀ a b : Except ExceptionObject α, OutcomeRelated Eq a b ↔ a = b := by
    intro a b
    cases a <;> cases b <;> simp [OutcomeRelated]
  constructor
  · intro h a
    constructor
    · intro ha
      obtain ⟨b, hb, hr⟩ := h.1 _ ha
      exact (same _ _).mp hr ▸ hb
    · intro hb
      obtain ⟨b, ha, hr⟩ := h.2 _ hb
      exact (same _ _).mp hr ▸ ha
  · intro h
    constructor
    · intro a ha
      exact ⟨a, (h a).mp ha, (same _ _).mpr rfl⟩
    · intro b hb
      exact ⟨b, (h b).mpr hb, (same _ _).mpr rfl⟩

end Execution

namespace Graph

/-- The actual Python definition, parsed through the existing Python AST bridge.
Lake's include_str dependency causes source edits to rebuild this definition. -/
def source : Module := python_data% (include_str "../graph_equivalence.py")

inductive Edge where
  | scalar (value : Constant)
  | ref (address : Nat)
deriving Repr

inductive Kind where
  | list | tuple | dict
  | object (typeIdentity : Nat)
deriving Repr

structure Node where
  kind : Kind
  labels : List String := []
  edges : List Edge := []
deriving Repr

structure Heap where
  roots : List Edge
  nodes : List Node
deriving Repr

def Edge.encode : Edge → Data
  | .scalar c => .list [.scalar (.string (Data.scalar c).typeName), .scalar c]
  | .ref n => .list [.scalar (.string "ref"), .scalar (.int n)]

def Kind.encode : Kind → Data
  | .list => .scalar (.string "list")
  | .tuple => .scalar (.string "tuple")
  | .dict => .scalar (.string "dict")
  | .object identity => .list [.scalar (.string "object"), .scalar (.int identity)]

def Node.encode (node : Node) : Data :=
  .list [node.kind.encode, .list (node.labels.map (Data.scalar ∘ Constant.string)),
    .list (node.edges.map Edge.encode)]

def Heap.encode (heap : Heap) : Data :=
  .list [.list (heap.roots.map Edge.encode), .list (heap.nodes.map Node.encode)]

/-- Run the Python comparator. A finite observation limit is only a testing tool;
the meaning of Equivalent below has no execution-fuel cutoff. -/
def compare (left right : Data) : Execution Data :=
  dataFunction source "same_snapshot" [left, right]

/-- The interpreted Python function must actually return True. Unsupported code,
errors, divergence, and an exhausted test budget never count as equivalence. -/
def Equivalent (left right : Data) : Prop :=
  Finishes (compare left right).step (compare left right).initial (.ok (.scalar (.bool true)))

/-- A test result distinguishes False from an unfinished or invalid comparison. -/
def observedBool : Execution.Observation Data → Option Bool
  | .done (.ok (.scalar (.bool b))) => some b
  | _ => none

theorem observation_of_bool {observation : Execution.Observation Data}
    (h : observedBool observation = some b) :
    observation = .done (.ok (.scalar (.bool b))) := by
  cases observation with
  | pending | unsupported => simp [observedBool] at h
  | done outcome =>
    cases outcome with
    | error _ => simp [observedBool] at h
    | ok value =>
      cases value with
      | list _ | type _ => simp [observedBool] at h
      | scalar c => cases c <;> simp_all [observedBool]

theorem equivalent_of_observe
    (h : observedBool ((compare left right).observe fuel) = some true) : Equivalent left right :=
  Execution.finishes_of_observe (observation_of_bool h)

theorem not_equivalent_of_observe
    (h : observedBool ((compare left right).observe fuel) = some false) : ¬ Equivalent left right := by
  intro equivalent
  have finished := Execution.finishes_of_observe (observation_of_bool h)
  have impossible := equivalent.unique finished
  cases impossible

/-- Equivalence of executions returning snapshots of all observable roots. -/
abbrev Equiv (left right : Execution Data) : Prop :=
  Execution.EquivBy Equivalent left right

/-- The scalar fast path is checked against the Python AST for arbitrary integers. -/
theorem compare_int (a b : Int) :
    (compare (.scalar (.int a)) (.scalar (.int b))).observe 4 =
      .done (.ok (.scalar (.bool (decide (a = b))))) := by
  simp [compare, source, dataFunction, findFunctionIn, executableBody,
    Execution.observe, Execution.observeFrom, dataStep, dataExpr, Data.equal,
    Data.typeName, Data.truth, scalarTruth, scalarCompare, evalCmpOp, List.lookup,
    bind, pure, Except.bind, Except.map, Functor.map]

@[simp] theorem equivalent_int (a b : Int) :
    Equivalent (.scalar (.int a)) (.scalar (.int b)) ↔ a = b := by
  have finished := Execution.finishes_of_observe (compare_int a b)
  constructor
  · intro h
    have unique := h.unique finished
    simpa using unique.symm
  · intro h
    subst b
    exact (by simpa using finished)

/-- The existing scalar execution backend's equality is also an exact fast path
for this Python relation, including the distinction between booleans and ints. -/
theorem compare_scalar (a b : Constant) :
    (compare (.scalar a) (.scalar b)).observe 4 =
      .done (.ok (.scalar (.bool (decide (a = b))))) := by
  cases a <;> cases b <;>
    simp [compare, source, dataFunction, findFunctionIn, executableBody,
      Execution.observe, Execution.observeFrom, dataStep, dataExpr, Data.equal,
      Data.typeName, Data.truth, scalarTruth, scalarCompare, evalCmpOp, List.lookup,
      bind, pure, Except.bind, Except.map, Functor.map]

  case bool.bool a b => cases a <;> cases b <;> decide

@[simp] theorem equivalent_scalar (a b : Constant) :
    Equivalent (.scalar a) (.scalar b) ↔ a = b := by
  have finished := Execution.finishes_of_observe (compare_scalar a b)
  constructor
  · intro h
    have unique := h.unique finished
    simpa using unique.symm
  · intro h
    subst b
    exact (by simpa using finished)

theorem scalar_equiv_iff (left right : Execution Constant) :
    Execution.EquivBy (fun a b => Equivalent (.scalar a) (.scalar b)) left right ↔
      left.Equiv right := by
  simp only [equivalent_scalar]
  exact Execution.equivBy_eq_iff left right

end Graph
end FormalSW.PyAst
