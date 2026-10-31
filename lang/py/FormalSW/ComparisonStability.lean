import lang.py.FormalSW.ComparisonRelocation

/-! Finite stabilization of recursive comparisons, without changing runtime fuel. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

/-- The finite-resolution argument also applies to a list of arbitrary coordinates. -/
theorem finite_resolution_stable_on {α ι : Type} (domain : List ι)
    (resolve : Nat → ι → Option α)
    (extension : ∀ fuel index, index ∈ domain →
      ResolutionExtends (resolve fuel index) (resolve (fuel + 1) index))
    (step : ∀ fuel, (∀ index ∈ domain, resolve (fuel + 1) index = resolve fuel index) →
      ∀ index ∈ domain, resolve (fuel + 2) index = resolve (fuel + 1) index) :
    ∀ index ∈ domain, resolve (domain.length + 1) index = resolve domain.length index := by
  have indexed := finite_resolution_stable domain.length
    (fun fuel index => domain[index]?.bind (resolve fuel))
    (by
      intro fuel index inside
      simpa only [List.getElem?_eq_getElem inside, Option.bind_some] using
        extension fuel domain[index] (List.getElem_mem inside))
    (by
      intro fuel same index inside
      have all : ∀ item ∈ domain, resolve (fuel + 1) item = resolve fuel item := by
        intro item member
        obtain ⟨position, bound, rfl⟩ := List.mem_iff_getElem.mp member
        simpa only [List.getElem?_eq_getElem bound, Option.bind_some] using same position bound
      simpa only [List.getElem?_eq_getElem inside, Option.bind_some] using
        step fuel all domain[index] (List.getElem_mem inside))
  intro item member
  obtain ⟨index, inside, rfl⟩ := List.mem_iff_getElem.mp member
  simpa only [List.getElem?_eq_getElem inside, Option.bind_some] using indexed index inside

/-- Positive fuel fixes scalar, mixed, and missing-reference cases immediately. -/
theorem compare_positive_congr (heap : Heap) (first second : Nat)
    (same : ∀ equality left right, left < heap.length → right < heap.length →
      HeapSort.compare (first + 1) heap equality (.ref left) (.ref right) =
        HeapSort.compare (second + 1) heap equality (.ref left) (.ref right))
    (equality : Bool) (left right : Value) :
    HeapSort.compare (first + 1) heap equality left right =
      HeapSort.compare (second + 1) heap equality left right := by
  cases left with
  | scalar left =>
    cases right with
    | scalar right => rfl
    | ref right =>
      cases found : heap[right]? with
      | none => simp only [HeapSort.compare, found]
      | some object => cases object <;> simp only [HeapSort.compare, found]
  | ref left =>
    cases right with
    | scalar right =>
      cases found : heap[left]? with
      | none => simp only [HeapSort.compare, found]
      | some object => cases object <;> simp only [HeapSort.compare, found]
    | ref right =>
      by_cases leftInside : left < heap.length
      · by_cases rightInside : right < heap.length
        · exact same equality left right leftInside rightInside
        · have missing : heap[right]? = none := List.getElem?_eq_none (by omega)
          cases found : heap[left]? with
          | none => simp only [HeapSort.compare, found]
          | some object => cases object <;> simp only [HeapSort.compare, found, missing]
      · have missing : heap[left]? = none := List.getElem?_eq_none (by omega)
        simp only [HeapSort.compare, missing]

/-- A stationary comparison table stays stationary at its next iteration. -/
theorem compare_step_congr (heap : Heap) (first second : Nat)
    (same : ∀ equality left right,
      HeapSort.compare first heap equality left right = HeapSort.compare second heap equality left right)
    (equality : Bool) (left right : Value) :
    HeapSort.compare (first + 1) heap equality left right =
      HeapSort.compare (second + 1) heap equality left right := by
  have equal := funext (fun left => funext (fun right => same true left right))
  have less := funext (fun left => funext (fun right => same false left right))
  cases left with
  | scalar left =>
    cases right with
    | scalar right => rfl
    | ref right =>
      cases found : heap[right]? with
      | none => simp only [HeapSort.compare, found]
      | some object => cases object <;> simp only [HeapSort.compare, found]
  | ref left =>
    cases right with
    | scalar right =>
      cases found : heap[left]? with
      | none => simp only [HeapSort.compare, found]
      | some object => cases object <;> simp only [HeapSort.compare, found]
    | ref right =>
      cases found : heap[left]? with
      | none => simp only [HeapSort.compare, found]
      | some object =>
        cases other : heap[right]? with
        | none => cases object <;> simp only [HeapSort.compare, found, other]
        | some otherObject =>
          cases object <;> cases otherObject <;>
            simp only [HeapSort.compare, found, other, equal, less]

/-- All recursive dependencies are comparisons of two actual heap addresses. -/
def comparisonCoordinates (size : Nat) : List (Bool × Nat × Nat) :=
  [true, false].flatMap fun equality =>
    (List.range size).flatMap fun left => (List.range size).map fun right => (equality, left, right)

theorem mem_comparisonCoordinates (size : Nat) (equality : Bool) (left right : Nat) :
    (equality, left, right) ∈ comparisonCoordinates size ↔ left < size ∧ right < size := by
  cases equality <;> simp [comparisonCoordinates]

theorem length_comparisonCoordinates (size : Nat) :
    (comparisonCoordinates size).length = 2 * size * size := by
  simp [comparisonCoordinates, List.length_flatMap, List.map_const', List.sum_replicate_nat,
    Nat.two_mul, Nat.add_mul]

/-- This is a proof bound, not the interpreter's native heap-length allowance.
It covers cycles, unsupported comparisons, exceptions, and even dangling references. -/
theorem compare_stabilized (heap : Heap) (extra : Nat) (equality : Bool) (left right : Value) :
    HeapSort.compare (2 * heap.length * heap.length + 1 + extra) heap equality left right =
      HeapSort.compare (2 * heap.length * heap.length + 1) heap equality left right := by
  let limit := 2 * heap.length * heap.length
  have adjacent := finite_resolution_stable_on (comparisonCoordinates heap.length)
    (fun fuel (equality, left, right) => HeapSort.compare (fuel + 1) heap equality (.ref left) (.ref right))
    (fun fuel (equality, left, right) _ => compare_step_extends heap (fuel + 1) equality (.ref left) (.ref right))
    (by
      intro fuel same coordinate member
      have all := compare_positive_congr heap (fuel + 1) fuel
        (fun equality left right hl hr => same (equality, left, right)
          ((mem_comparisonCoordinates _ _ _ _).mpr ⟨hl, hr⟩))
      exact compare_step_congr heap (fuel + 2) (fuel + 1) all coordinate.1
        (.ref coordinate.2.1) (.ref coordinate.2.2))
  rw [length_comparisonCoordinates] at adjacent
  have base : ∀ equality left right,
      HeapSort.compare (limit + 2) heap equality left right =
        HeapSort.compare (limit + 1) heap equality left right :=
    compare_positive_congr heap (limit + 1) limit
      (fun equality left right hl hr => adjacent (equality, left, right)
        ((mem_comparisonCoordinates _ _ _ _).mpr ⟨hl, hr⟩))
  change HeapSort.compare (limit + 1 + extra) heap equality left right = _
  induction extra generalizing equality left right with
  | zero => rfl
  | succ extra ih =>
    exact (compare_step_congr heap (limit + 1 + extra) (limit + 1) ih equality left right).trans
      (base equality left right)

/-- The finite table detects exactly those comparisons that never resolve at any fuel. -/
theorem compare_stabilized_none_iff (heap : Heap) (equality : Bool) (left right : Value) :
    HeapSort.compare (2 * heap.length * heap.length + 1) heap equality left right = none ↔
      ∀ fuel, HeapSort.compare fuel heap equality left right = none := by
  constructor
  · intro unresolved fuel
    cases found : HeapSort.compare fuel heap equality left right with
    | none => rfl
    | some outcome =>
      have later := compare_extends heap fuel (2 * heap.length * heap.length + 1)
        equality left right outcome found
      rw [Nat.add_comm, compare_stabilized, unresolved] at later
      cases later
  · intro unresolved
    exact unresolved _

/-- Any finite completion is already visible in the stabilized comparison table. -/
theorem compare_stabilized_result_iff (heap : Heap) (equality : Bool) (left right : Value)
    (outcome : Except ExceptionObject Bool) :
    HeapSort.compare (2 * heap.length * heap.length + 1) heap equality left right = some outcome ↔
      ∃ fuel, HeapSort.compare fuel heap equality left right = some outcome := by
  constructor
  · intro completed
    exact ⟨_, completed⟩
  · rintro ⟨fuel, completed⟩
    have later := compare_extends heap fuel (2 * heap.length * heap.length + 1)
      equality left right outcome completed
    simpa only [Nat.add_comm fuel, compare_stabilized] using later

/-- Stabilized comparisons agree across layouts, including unsupported results.
The separate claim at each heap's native linear allowance is not assumed here. -/
theorem RuntimeLayout.compare_stabilized {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (equality : Bool) (left right : Value)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length) :
    HeapSort.compare (2 * physical.length * physical.length + 1) physical equality
        (relocateValue rename left) (relocateValue rename right) =
      HeapSort.compare (2 * logical.length * logical.length + 1) logical equality left right := by
  let logicalFuel := 2 * logical.length * logical.length + 1
  let physicalFuel := 2 * physical.length * physical.length + 1
  calc
    _ = HeapSort.compare (physicalFuel + logicalFuel) physical equality
        (relocateValue rename left) (relocateValue rename right) :=
      (Mutable.Relocation.compare_stabilized physical logicalFuel equality _ _).symm
    _ = HeapSort.compare (physicalFuel + logicalFuel) logical equality left right :=
      layout.compareFuel closed _ equality left right leftInside rightInside
    _ = _ := by
      rw [Nat.add_comm]
      exact Mutable.Relocation.compare_stabilized logical physicalFuel equality left right

/-- A comparison unresolved in the finite table remains unsupported at every relocated fuel. -/
theorem RuntimeLayout.compare_stabilized_unresolved {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (equality : Bool) (left right : Value)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length)
    (unresolved : HeapSort.compare (2 * logical.length * logical.length + 1)
      logical equality left right = none) (fuel : Nat) :
    HeapSort.compare fuel physical equality (relocateValue rename left) (relocateValue rename right) = none := by
  rw [layout.compareFuel closed fuel equality left right leftInside rightInside]
  exact (compare_stabilized_none_iff logical equality left right).mp unresolved fuel

end FormalSW.PyAst.Mutable.Relocation
