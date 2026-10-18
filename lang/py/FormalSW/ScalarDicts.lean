import lang.py.FormalSW.ScalarSets

/-! Insertion-ordered dictionaries with builtin scalar keys and arbitrary values.
Equal numeric keys share an entry; replacement retains its first key and position. -/
namespace FormalSW.PyAst.ScalarDict

def lookup (entries : List (Constant × α)) (key : Constant) : Option α :=
  match entries with
  | [] => none
  | (stored, value) :: rest =>
      if (scalarCompare .eq stored key).getD false then some value else lookup rest key

def insert (entries : List (Constant × α)) (key : Constant) (value : α) : List (Constant × α) :=
  match entries with
  | [] => [(key, value)]
  | (stored, previous) :: rest =>
      if (scalarCompare .eq stored key).getD false then (stored, value) :: rest
      else (stored, previous) :: insert rest key value

def Valid (entries : List (Constant × α)) : Prop :=
  ScalarSet.Valid (entries.map Prod.fst)

theorem lookup_insert_self (entries : List (Constant × α)) (key : Constant) (value : α) :
    lookup (insert entries key value) key = some value := by
  have reflexive : scalarCompare .eq key key = some true := by
    cases key <;> simp [scalarCompare, evalCmpOp]
  induction entries with
  | nil => simp [insert, lookup, reflexive]
  | cons entry rest ih =>
      obtain ⟨stored, previous⟩ := entry
      simp only [insert]
      split <;> simp_all [lookup]

/-- A successful lookup selects a value from an existing entry. -/
theorem lookup_property (entries : List (Constant × α)) (key : Constant) (property : α → Prop)
    (typed : ∀ entry ∈ entries, property entry.2) (found : lookup entries key = some value) :
    property value := by
  induction entries with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
      obtain ⟨stored, previous⟩ := entry
      simp only [lookup] at found
      split at found
      · cases found
        exact typed (stored, value) (by simp)
      · exact ih (by intro entry member; exact typed entry (by simp [member])) found

/-- Replacement retains the old key representative and the new value's domain. -/
theorem insert_property (entries : List (Constant × α)) (key : Constant) (value : α)
    (keyProperty : Constant → Prop) (valueProperty : α → Prop)
    (typed : ∀ entry ∈ entries, keyProperty entry.1 ∧ valueProperty entry.2)
    (newKey : keyProperty key) (newValue : valueProperty value) :
    ∀ entry ∈ insert entries key value, keyProperty entry.1 ∧ valueProperty entry.2 := by
  induction entries with
  | nil => simpa [insert] using And.intro newKey newValue
  | cons entry rest ih =>
      obtain ⟨stored, previous⟩ := entry
      have head := typed (stored, previous) (by simp)
      have tail : ∀ entry ∈ rest, keyProperty entry.1 ∧ valueProperty entry.2 := by
        intro entry member
        exact typed entry (by simp [member])
      simp only [insert]
      split
      · simpa using And.intro (And.intro head.1 newValue) tail
      · simpa using And.intro head (ih tail)

end FormalSW.PyAst.ScalarDict
