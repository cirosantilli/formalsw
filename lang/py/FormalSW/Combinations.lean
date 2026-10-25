import lang.py.FormalSW.Permutations

/-! Positional combinations in input-index order, retaining repeated values at distinct positions. -/
namespace FormalSW.PyAst.Combinations

/-- Include the next position before skipping it, as in itertools.combinations. -/
def rows : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | count + 1, first :: rest =>
      (rows count rest).map (first :: ·) ++ rows (count + 1) rest
termination_by _ items => items.length

theorem rows_map (f : α → β) (count : Nat) (items : List α) :
    rows count (items.map f) = (rows count items).map (List.map f) := by
  induction items generalizing count with
  | nil => cases count <;> simp [rows]
  | cons first rest ih =>
      cases count with
      | zero => simp [rows]
      | succ count => simp [rows, ih, List.map_map, Function.comp_def]

theorem mem_rows_iff (count : Nat) (items row : List α) :
    row ∈ rows count items ↔ row.Sublist items ∧ row.length = count := by
  induction items generalizing count row with
  | nil =>
      cases count with
      | zero => simp [rows]
      | succ count => simp [rows]; rintro rfl; simp
  | cons first rest ih =>
      cases count with
      | zero => simp [rows]; rintro rfl; exact List.nil_sublist _
      | succ count =>
          simp only [rows, List.mem_append, List.mem_map, ih]
          constructor
          · rintro (⟨tail, ⟨sublist, length⟩, rfl⟩ | ⟨sublist, length⟩)
            · exact ⟨sublist.cons_cons first, by simp [length]⟩
            · exact ⟨sublist.cons first, length⟩
          · rintro ⟨selected, length⟩
            rcases List.sublist_cons_iff.mp selected with skipped | ⟨tail, same, kept⟩
            · exact Or.inr ⟨skipped, length⟩
            · subst row
              exact Or.inl ⟨tail, ⟨kept, by simpa using length⟩, rfl⟩

abbrev Cursor := Permutations.Cursor

/-- Snapshot the input pool, then validate the required length. -/
def acquire (source length : Mutable.Value) : Mutable.Eval Cursor := do
  match source with
  | .ref address =>
      match (← get)[address]? with
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => Mutable.unsupported
      | _ => pure ()
  | _ => pure ()
  let pool ← Mutable.sequence source
  match length with
  | .scalar .none => Mutable.error "TypeError"
  | _ =>
      let count ← Permutations.size pool.length length
      return ⟨rows count pool⟩

theorem acquire_list (heap : Mutable.Heap) (address count : Nat) (items : List Mutable.Value)
    (found : heap[address]? = some (.list items)) :
    acquire (.ref address) (.scalar (.int count)) heap =
      some (.ok ⟨rows count items⟩, heap) := by
  simp [acquire, Mutable.sequence, found, Permutations.size, Except.map,
    show ¬ (count : Int) < 0 by omega]

end FormalSW.PyAst.Combinations
