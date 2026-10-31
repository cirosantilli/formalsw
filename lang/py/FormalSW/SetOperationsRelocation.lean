import lang.py.FormalSW.ConstructionRelocation

/-! Allocating and augmented set operations retain corresponding identities and aliases. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

variable {logical physical : Heap} {rename : Nat → Nat}

/-- The shared allocation/update branch of the actual scalar-set operators. -/
def storeSetResult (address : Nat) (items : List Constant) (inPlace : Bool) : Eval Value := do
  if inPlace then
    modify fun heap => heap.set address (.set items)
    return .ref address
  else Mutable.allocateSet items

theorem ExecutionLayout.storeSetResult (layout : ExecutionLayout logical physical rename)
    (address : Nat) (before items : List Constant) (inPlace : Bool)
    (found : logical[address]? = some (.set before))
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : storeSetResult address items inPlace logical = some (outcome, after)) :
    ∃ other nextMap,
      storeSetResult (rename address) items inPlace physical =
        some (outcome.map (relocateValue nextMap), other) ∧
      ExecutionLayout after other nextMap ∧
      (∀ index < logical.length, nextMap index = rename index) ∧
      logical.length ≤ after.length ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have addressInside := (List.getElem?_eq_some_iff.mp found).1
  cases inPlace with
  | false =>
    have same : some (.ok (.ref logical.length), logical ++ [.set items]) = some (outcome, after) := executed
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
    refine ⟨physical ++ [.set items], extendMap rename logical.length physical.length, ?_,
      (layout.allocateSet items).2.2, fun _ bound => extendMap_old _ _ _ _ bound, by simp, ?_⟩
    · simp [Relocation.storeSetResult, Mutable.allocateSet, relocateValue, Except.map]
    · intro returned equal
      have same : returned = .ref logical.length := by simpa using equal.symm
      simp [same, Value.edge, Graph.Edge.Within]
  | true =>
    have same : some (.ok (.ref address), logical.set address (.set items)) = some (outcome, after) := executed
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
    refine ⟨physical.set (rename address) (.set items), rename, ?_,
      layout.set_nonempty address (.set before) (.set items) found (by simp) (by simp)
        (by simp [ObjectWithin, objectValues]), fun _ _ => rfl, by simp, ?_⟩
    · simp [Relocation.storeSetResult, relocateValue, Except.map]
    · intro returned equal
      have same : returned = .ref address := by simpa using equal.symm
      simpa [same, Value.edge, Graph.Edge.Within] using addressInside

theorem setUnion_result (heap : Heap) (left right : Nat) (xs ys : List Constant) (inPlace : Bool)
    (leftFound : heap[left]? = some (.set xs)) (rightFound : heap[right]? = some (.set ys)) :
    Mutable.setUnion left right inPlace heap = storeSetResult left (ScalarSet.union xs ys) inPlace heap := by
  simp [Mutable.setUnion, storeSetResult, leftFound, rightFound]

theorem setDifference_result (heap : Heap) (left right : Nat) (xs ys : List Constant) (inPlace : Bool)
    (leftFound : heap[left]? = some (.set xs)) (rightFound : heap[right]? = some (.set ys)) :
    Mutable.setDifference left right inPlace heap = storeSetResult left (ScalarSet.difference xs ys) inPlace heap := by
  simp [Mutable.setDifference, storeSetResult, leftFound, rightFound]

/-- Operator dispatch uses container kind, never its reference-bearing payload. -/
inductive SetOperand where
  | scalars (items : List Constant)
  | keys
  | custom
  | other

def setOperand : Object → SetOperand
  | .set items => .scalars items
  | .keySet _ => .keys
  | .instance _ _ _ | .dataInstance _ _ _ _ _ => .custom
  | _ => .other

theorem setOperand_relocates (object : Object) (rename : Nat → Nat) :
    setOperand (relocateObject rename object) = setOperand object := by
  cases object <;> rfl

def unionOperands (address : Nat) (left right : SetOperand) (inPlace : Bool) : Eval Value :=
  match left, right with
  | .scalars xs, .scalars ys => storeSetResult address (ScalarSet.union xs ys) inPlace
  | _, _ => unsupported

def differenceOperands (address : Nat) (left right : SetOperand) (inPlace : Bool) : Eval Value :=
  match left, right with
  | .scalars xs, .scalars ys => storeSetResult address (ScalarSet.difference xs ys) inPlace
  | .scalars _, .keys | .keys, .scalars _ | .keys, .keys | .custom, _ | _, .custom => unsupported
  | _, _ => error "TypeError"

theorem setUnion_operands (heap : Heap) (left right : Nat) (leftObject rightObject : Object) (inPlace : Bool)
    (leftFound : heap[left]? = some leftObject) (rightFound : heap[right]? = some rightObject) :
    Mutable.setUnion left right inPlace heap =
      unionOperands left (setOperand leftObject) (setOperand rightObject) inPlace heap := by
  change (match heap[left]?, heap[right]? with
    | some (.set xs), some (.set ys) => storeSetResult left (ScalarSet.union xs ys) inPlace
    | _, _ => unsupported) heap = _
  rw [leftFound, rightFound]
  cases leftObject <;> cases rightObject <;> rfl

theorem setDifference_operands (heap : Heap) (left right : Nat) (leftObject rightObject : Object) (inPlace : Bool)
    (leftFound : heap[left]? = some leftObject) (rightFound : heap[right]? = some rightObject) :
    Mutable.setDifference left right inPlace heap =
      differenceOperands left (setOperand leftObject) (setOperand rightObject) inPlace heap := by
  change (match heap[left]?, heap[right]? with
    | some (.set xs), some (.set ys) => storeSetResult left (ScalarSet.difference xs ys) inPlace
    | some (.set _), some (.keySet _) | some (.keySet _), some (.set _)
      | some (.keySet _), some (.keySet _) => unsupported
    | some (.instance _ _ _), _ | _, some (.instance _ _ _)
      | some (.dataInstance _ _ _ _ _), _ | _, some (.dataInstance _ _ _ _ _) => unsupported
    | none, _ | _, none => unsupported
    | _, _ => error "TypeError") heap = _
  rw [leftFound, rightFound]
  cases leftObject <;> cases rightObject <;> rfl

/-- A scalar-set classification supplies the exact original storage form. -/
theorem setOperand_scalars (object : Object) (items : List Constant)
    (classified : setOperand object = .scalars items) : object = .set items := by
  cases object <;> simp [setOperand] at classified ⊢
  exact classified

/-- Union transports the actual allocating or in-place result, allowing the operands to alias. -/
theorem ExecutionLayout.setUnion (layout : ExecutionLayout logical physical rename)
    (left right : Nat) (inPlace : Bool) (leftInside : left < logical.length) (rightInside : right < logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.setUnion left right inPlace logical = some (outcome, after)) :
    ∃ other nextMap,
      Mutable.setUnion (rename left) (rename right) inPlace physical =
        some (outcome.map (relocateValue nextMap), other) ∧
      ExecutionLayout after other nextMap ∧
      (∀ index < logical.length, nextMap index = rename index) ∧
      logical.length ≤ after.length ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have leftFound : logical[left]? = some logical[left] := List.getElem?_eq_getElem leftInside
  have rightFound : logical[right]? = some logical[right] := List.getElem?_eq_getElem rightInside
  have movedLeft := layout.runtime.lookup left _ leftFound
  have movedRight := layout.runtime.lookup right _ rightFound
  rw [setUnion_operands logical left right _ _ inPlace leftFound rightFound] at executed
  simp only [setUnion_operands physical (rename left) (rename right) _ _ inPlace movedLeft movedRight,
    setOperand_relocates]
  cases leftKind : setOperand logical[left] <;>
    try (solve | simp [unionOperands, leftKind, unsupported] at executed)
  rename_i xs
  cases rightKind : setOperand logical[right] <;>
    try (solve | simp [unionOperands, leftKind, rightKind, unsupported] at executed)
  rename_i ys
  have original := setOperand_scalars _ xs leftKind
  have found : logical[left]? = some (.set xs) := by simpa only [original] using leftFound
  have run : Relocation.storeSetResult left (ScalarSet.union xs ys) inPlace logical = some (outcome, after) := by
    simpa only [leftKind, rightKind, unionOperands] using executed
  simpa only [leftKind, rightKind, unionOperands] using
    layout.storeSetResult left xs (ScalarSet.union xs ys) inPlace found _ _ run

theorem RuntimeLayout.setUnion_unsupported (layout : RuntimeLayout logical physical rename)
    (left right : Nat) (inPlace : Bool) (leftInside : left < logical.length) (rightInside : right < logical.length) :
    Mutable.setUnion (rename left) (rename right) inPlace physical = none ↔
      Mutable.setUnion left right inPlace logical = none := by
  have leftFound : logical[left]? = some logical[left] := List.getElem?_eq_getElem leftInside
  have rightFound : logical[right]? = some logical[right] := List.getElem?_eq_getElem rightInside
  rw [setUnion_operands logical left right _ _ inPlace leftFound rightFound,
    setUnion_operands physical (rename left) (rename right) _ _ inPlace
      (layout.lookup left _ leftFound) (layout.lookup right _ rightFound)]
  simp only [setOperand_relocates]
  cases setOperand logical[left] <;> cases setOperand logical[right] <;> cases inPlace <;>
    simp [unionOperands, storeSetResult, Mutable.allocateSet, unsupported]

/-- Difference also preserves modeled TypeError exits and every unrelated heap cell. -/
theorem ExecutionLayout.setDifference (layout : ExecutionLayout logical physical rename)
    (left right : Nat) (inPlace : Bool) (leftInside : left < logical.length) (rightInside : right < logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.setDifference left right inPlace logical = some (outcome, after)) :
    ∃ other nextMap,
      Mutable.setDifference (rename left) (rename right) inPlace physical =
        some (outcome.map (relocateValue nextMap), other) ∧
      ExecutionLayout after other nextMap ∧
      (∀ index < logical.length, nextMap index = rename index) ∧
      logical.length ≤ after.length ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have leftFound : logical[left]? = some logical[left] := List.getElem?_eq_getElem leftInside
  have rightFound : logical[right]? = some logical[right] := List.getElem?_eq_getElem rightInside
  have movedLeft := layout.runtime.lookup left _ leftFound
  have movedRight := layout.runtime.lookup right _ rightFound
  rw [setDifference_operands logical left right _ _ inPlace leftFound rightFound] at executed
  simp only [setDifference_operands physical (rename left) (rename right) _ _ inPlace movedLeft movedRight,
    setOperand_relocates]
  cases leftKind : setOperand logical[left] <;> cases rightKind : setOperand logical[right]
  all_goals try (solve | simp [differenceOperands, leftKind, rightKind, unsupported] at executed)
  case scalars.scalars xs ys =>
    have original := setOperand_scalars _ xs leftKind
    have found : logical[left]? = some (.set xs) := by simpa only [original] using leftFound
    have run : Relocation.storeSetResult left (ScalarSet.difference xs ys) inPlace logical = some (outcome, after) := by
      simpa only [leftKind, rightKind, differenceOperands] using executed
    simpa only [leftKind, rightKind, differenceOperands] using
      layout.storeSetResult left xs (ScalarSet.difference xs ys) inPlace found _ _ run
  all_goals
    have result : some (.error {typeName := "TypeError", args := []}, logical) = some (outcome, after) := by
      simpa [differenceOperands, leftKind, rightKind, error] using executed
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj result)
    refine ⟨physical, rename, ?_, layout, fun _ _ => rfl, Nat.le_refl _, ?_⟩
    · simp [differenceOperands, error, Except.map]
    · intro returned impossible
      cases impossible

theorem RuntimeLayout.setDifference_unsupported (layout : RuntimeLayout logical physical rename)
    (left right : Nat) (inPlace : Bool) (leftInside : left < logical.length) (rightInside : right < logical.length) :
    Mutable.setDifference (rename left) (rename right) inPlace physical = none ↔
      Mutable.setDifference left right inPlace logical = none := by
  have leftFound : logical[left]? = some logical[left] := List.getElem?_eq_getElem leftInside
  have rightFound : logical[right]? = some logical[right] := List.getElem?_eq_getElem rightInside
  rw [setDifference_operands logical left right _ _ inPlace leftFound rightFound,
    setDifference_operands physical (rename left) (rename right) _ _ inPlace
      (layout.lookup left _ leftFound) (layout.lookup right _ rightFound)]
  simp only [setOperand_relocates]
  cases setOperand logical[left] <;> cases setOperand logical[right] <;> cases inPlace <;>
    simp [differenceOperands, storeSetResult, Mutable.allocateSet, unsupported, error]

end FormalSW.PyAst.Mutable.Relocation
