import lang.py.FormalSW.MutableGlobals

/-! Finite positional permutations. The pool is a shallow snapshot; tuple
allocation occurs only when an item is requested. Equal values at different
positions are separate choices, as in itertools.permutations. -/
namespace FormalSW.PyAst.Permutations

/-- Choose each position from left to right, retaining the order of the rest. -/
def choices : List α → List (α × List α)
  | [] => []
  | first :: rest => (first, rest) :: (choices rest).map fun (value, remaining) =>
      (value, first :: remaining)

@[simp] theorem choices_length (items : List α) : (choices items).length = items.length := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp [choices, ih]

theorem choices_map (f : α → β) (items : List α) :
    choices (items.map f) = (choices items).map (fun (value, remaining) => (f value, remaining.map f)) := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp [choices, ih, List.map_map, Function.comp_def]

theorem choice_length (selected : (value, remaining) ∈ choices items) :
    remaining.length + 1 = items.length := by
  induction items generalizing remaining with
  | nil => simp [choices] at selected
  | cons first rest ih =>
      simp only [choices, List.mem_cons, List.mem_map] at selected
      rcases selected with equal | ⟨⟨other, tail⟩, member, equal⟩
      · cases equal
        rfl
      · cases equal
        simpa using ih member

/-- Each recursive block fixes the next input position. -/
def rows : Nat → List α → List (List α)
  | 0, _ => [[]]
  | size + 1, items => (choices items).flatMap fun (value, remaining) =>
      (rows size remaining).map (value :: ·)

theorem rows_map (f : α → β) (length : Nat) (items : List α) :
    rows length (items.map f) = (rows length items).map (List.map f) := by
  induction length generalizing items with
  | zero => rfl
  | succ length ih =>
      simp [rows, choices_map, List.flatMap_map, List.map_flatMap, List.map_map,
        ih, Function.comp_def]

/-- Number of ordered selections without replacement, including empty pools. -/
def count : Nat → Nat → Nat
  | _, 0 => 1
  | size, length + 1 => size * count (size - 1) length

theorem rows_length (length : Nat) (items : List α) :
    (rows length items).length = count items.length length := by
  induction length generalizing items with
  | zero => rfl
  | succ length ih =>
      simp only [rows, List.length_flatMap, List.length_map, count]
      have constant : (choices items).map (fun pair => (rows length pair.2).length) =
          (choices items).map (fun _ => count (items.length - 1) length) := by
        apply List.map_congr_left
        intro pair member
        rw [ih]
        have size := choice_length member
        congr 1
        omega
      rw [constant]
      have total (entries : List (α × List α)) :
          (entries.map fun _ => count (items.length - 1) length).sum =
            entries.length * count (items.length - 1) length := by
        induction entries with
        | nil => simp
        | cons first rest ih => simp [ih, Nat.succ_mul, Nat.add_comm]
      rw [total, choices_length]

theorem row_length (member : row ∈ rows length items) : row.length = length := by
  induction length generalizing items row with
  | zero => simp [rows] at member; subst row; rfl
  | succ length ih =>
      simp only [rows, List.mem_flatMap, List.mem_map] at member
      obtain ⟨⟨value, remaining⟩, _, tail, inside, rfl⟩ := member
      simp [ih inside]

theorem choice_perm (selected : (value, remaining) ∈ choices items) :
    (value :: remaining).Perm items := by
  induction items generalizing remaining with
  | nil => simp [choices] at selected
  | cons first rest ih =>
      simp only [choices, List.mem_cons, List.mem_map] at selected
      rcases selected with equal | ⟨⟨other, tail⟩, member, equal⟩
      · cases equal
        exact .refl _
      · cases equal
        exact (List.Perm.swap _ _ _).trans ((ih member).cons first)

theorem choice_for_mem (member : value ∈ items) :
    ∃ remaining, (value, remaining) ∈ choices items := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨rest, List.mem_cons_self⟩
      · obtain ⟨remaining, selected⟩ := ih member
        refine ⟨first :: remaining, List.mem_cons_of_mem _ ?_⟩
        exact List.mem_map.mpr ⟨(value, remaining), selected, rfl⟩

theorem row_perm (length : Nat) (items row : List α) (size : items.length = length)
    (member : row ∈ rows length items) : row.Perm items := by
  induction length generalizing items row with
  | zero =>
      have empty : items = [] := List.eq_nil_of_length_eq_zero size
      subst items
      simp [rows] at member
      subst row
      exact .refl _
  | succ length ih =>
      simp only [rows, List.mem_flatMap, List.mem_map] at member
      obtain ⟨⟨value, remaining⟩, selected, tail, inside, rfl⟩ := member
      have shorter := choice_length selected
      exact ((ih remaining tail (by omega) inside).cons value).trans (choice_perm selected)

theorem mem_rows_full (permuted : row.Perm items) : row ∈ rows items.length items := by
  induction row generalizing items with
  | nil =>
      have empty : items = [] := List.eq_nil_of_length_eq_zero permuted.length_eq.symm
      subst items
      simp [rows]
  | cons first tail ih =>
      obtain ⟨remaining, selected⟩ := choice_for_mem (permuted.mem_iff.mp List.mem_cons_self)
      have tailPerm := (permuted.trans (choice_perm selected).symm).cons_inv
      have member := ih tailPerm
      rw [← choice_length selected, rows]
      exact List.mem_flatMap.mpr ⟨(first, remaining), selected, List.mem_map.mpr ⟨tail, member, rfl⟩⟩

theorem mem_rows_full_iff : row ∈ rows items.length items ↔ row.Perm items :=
  ⟨row_perm items.length items row rfl, mem_rows_full⟩

@[simp] theorem count_full (length : Nat) : count length length = Math.factorial length := by
  induction length with
  | zero => rfl
  | succ length ih => simpa [count, Math.factorial] using congrArg ((length + 1) * ·) ih

theorem rows_full_length (items : List α) :
    (rows items.length items).length = Math.factorial items.length := by
  rw [rows_length, count_full]

/-- A private iterator holds value references, not a live reference to the pool. -/
structure Cursor where
  remaining : List (List Mutable.Value)
deriving Repr, DecidableEq

def size (poolLength : Nat) : Mutable.Value → Mutable.Eval Nat
  | .scalar .none => pure poolLength
  | .scalar (.bool value) => pure (if value then 1 else 0)
  | .scalar (.int value) => if value < 0 then Mutable.error "ValueError" else pure value.toNat
  | _ => Mutable.error "TypeError"

/-- Snapshot the sequence before validating the optional length. -/
def acquire (source : Mutable.Value) (length : Mutable.Value := .scalar .none) : Mutable.Eval Cursor := do
  match source with
  | .ref address =>
      match (← get)[address]? with
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => Mutable.unsupported
      | _ => pure ()
  | _ => pure ()
  let pool ← Mutable.sequence source
  let length ← size pool.length length
  return ⟨rows length pool⟩

/-- Exhaustion allocates nothing; yielded tuples retain shared element identities. -/
def next (cursor : Cursor) : Mutable.Eval (Option (Mutable.Value × Cursor)) := do
  match cursor.remaining with
  | [] => return none
  | row :: remaining => return some (← Mutable.allocateTuple row, ⟨remaining⟩)

theorem acquire_list (heap : Mutable.Heap) (address : Nat) (items : List Mutable.Value)
    (found : heap[address]? = some (.list items)) :
    acquire (.ref address) (.scalar .none) heap = some (.ok ⟨rows items.length items⟩, heap) := by
  simp [acquire, Mutable.sequence, found, size, Except.map]

theorem next_exhausted (heap : Mutable.Heap) :
    next ⟨[]⟩ heap = some (.ok none, heap) := rfl

theorem next_nonempty (heap : Mutable.Heap) (first : Mutable.Value)
    (tail : List Mutable.Value) (remaining : List (List Mutable.Value)) :
    next ⟨(first :: tail) :: remaining⟩ heap =
      some (.ok (some (.ref heap.length, ⟨remaining⟩)), heap ++ [.tuple (first :: tail)]) := by
  simp [next, Mutable.allocateTuple, Except.map]

end FormalSW.PyAst.Permutations
