import lang.py.FormalSW.Calls

/-! Stable sorting of builtin scalars. Comparisons have no user callbacks or
side effects, and incompatible scalar types raise the modeled TypeError.
Sorting does not discard the runtime type of equal values such as True and 1. -/
namespace FormalSW.PyAst.ScalarSort

attribute [local simp] bind pure Functor.map Except.bind Except.map Except.pure

def insert (value : Constant) : List Constant → Except ExceptionObject (List Constant)
  | [] => .ok [value]
  | first :: rest => do
      match scalarCompare .lt first value with
      | none => .error { typeName := "TypeError", args := [] }
      | some true => return first :: (← insert value rest)
      | some false => return value :: first :: rest

/-- Insert earlier equal elements before later ones, preserving Python's stability. -/
def sort : List Constant → Except ExceptionObject (List Constant)
  | [] => .ok []
  | first :: rest => do insert first (← sort rest)

def insertInt (value : Int) : List Int → List Int
  | [] => [value]
  | first :: rest => if first < value then first :: insertInt value rest else value :: first :: rest

def ints (values : List Int) : List Int := values.foldr insertInt []

theorem insertInt_perm (value : Int) (values : List Int) :
    (insertInt value values).Perm (value :: values) := by
  induction values with
  | nil => exact .refl _
  | cons first rest ih =>
      by_cases smaller : first < value
      · simp only [insertInt, if_pos smaller]
        exact (ih.cons first).trans (.swap _ _ _)
      · simp only [insertInt, if_neg smaller]
        exact .refl _

theorem ints_perm (values : List Int) : (ints values).Perm values := by
  induction values with
  | nil => exact .refl _
  | cons first rest ih => exact (insertInt_perm first (ints rest)).trans (ih.cons first)

theorem insertInt_ordered (value : Int) (values : List Int)
    (ordered : values.Pairwise (· ≤ ·)) : (insertInt value values).Pairwise (· ≤ ·) := by
  induction values with
  | nil => simp [insertInt]
  | cons first rest ih =>
      obtain ⟨lower, tailOrdered⟩ := List.pairwise_cons.mp ordered
      by_cases smaller : first < value
      · simp only [insertInt, if_pos smaller, List.pairwise_cons]
        refine ⟨?_, ih tailOrdered⟩
        intro x member
        have member := (insertInt_perm value rest).mem_iff.mp member
        rcases List.mem_cons.mp member with rfl | member
        · omega
        · exact lower x member
      · simp only [insertInt, if_neg smaller, List.pairwise_cons]
        refine ⟨?_, lower, tailOrdered⟩
        intro x member
        rcases List.mem_cons.mp member with rfl | member
        · omega
        · have bound := lower x member
          omega

theorem ints_ordered (values : List Int) : (ints values).Pairwise (· ≤ ·) := by
  induction values with
  | nil => exact .nil
  | cons first rest ih => exact insertInt_ordered first (ints rest) ih

theorem insert_ints (value : Int) (values : List Int) :
    insert (.int value) (values.map Constant.int) = .ok ((insertInt value values).map Constant.int) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      by_cases smaller : first < value <;>
        simp [insert, insertInt, scalarCompare, evalCmpOp, smaller, ih]

theorem sort_ints (values : List Int) :
    sort (values.map Constant.int) = .ok ((ints values).map Constant.int) := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [sort, ih, insert_ints, ints]

/-- Sorting a triple whose last element is largest only orders the first two. -/
theorem three_top (a b c : Int) (ac : a ≤ c) (bc : b ≤ c) :
    sort [.int a, .int b, .int c] = .ok [.int (min a b), .int (max a b), .int c] := by
  have ca : ¬c < a := by omega
  have cb : ¬c < b := by omega
  by_cases ab : a ≤ b
  · have ba : ¬b < a := by omega
    simp [sort, insert, scalarCompare, evalCmpOp, cb, ba, Int.min_def, Int.max_def, ab]
  · have ba : b < a := by omega
    simp [sort, insert, scalarCompare, evalCmpOp, cb, ca, ba, Int.min_def, Int.max_def, ab]

/-- The same stable scalar sort on Unicode strings. -/
def insertString (value : String) : List String → List String
  | [] => [value]
  | first :: rest => if first < value then first :: insertString value rest else value :: first :: rest

def strings (values : List String) : List String := values.foldr insertString []

theorem insertString_perm (value : String) (values : List String) :
    (insertString value values).Perm (value :: values) := by
  induction values with
  | nil => exact .refl _
  | cons first rest ih =>
      by_cases smaller : first < value
      · simp only [insertString, if_pos smaller]
        exact (ih.cons first).trans (.swap _ _ _)
      · simp only [insertString, if_neg smaller]
        exact .refl _

theorem strings_perm (values : List String) : (strings values).Perm values := by
  induction values with
  | nil => exact .refl _
  | cons first rest ih => exact (insertString_perm first (strings rest)).trans (ih.cons first)

theorem insert_strings (value : String) (values : List String) :
    insert (.string value) (values.map Constant.string) = .ok ((insertString value values).map Constant.string) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      by_cases smaller : first < value <;>
        simp [insert, insertString, scalarCompare, evalCmpOp, smaller, ih]

theorem sort_strings (values : List String) :
    sort (values.map Constant.string) = .ok ((strings values).map Constant.string) := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [sort, ih, insert_strings, strings]

end FormalSW.PyAst.ScalarSort
