import lang.py.FormalSW.Calls
import lang.py.FormalSW.DataRuntime

/-! Sets of builtin immutable scalars. Membership uses Python equality, whereas
observation retains the type of the first inserted representative (True or 1).
The stored list is not a claim about Python's unspecified iteration order. -/
namespace FormalSW.PyAst.ScalarSet

def contains (items : List Constant) (value : Constant) : Bool :=
  items.any fun item => (scalarCompare .eq item value).getD false

def insert (items : List Constant) (value : Constant) : List Constant :=
  if contains items value then items else items ++ [value]

def Valid (items : List Constant) : Prop :=
  items.Pairwise fun left right => scalarCompare .eq left right = some false

def subset (left right : List Constant) : Bool :=
  left.all (contains right)

def compare (op : CmpOp) (left right : List Constant) : Bool :=
  match op with
  | .eq => subset left right && subset right left
  | .notEq => !(subset left right && subset right left)
  | .lt => subset left right && !subset right left
  | .ltE => subset left right
  | .gt => subset right left && !subset left right
  | .gtE => subset right left

/-- Canonicalize only the observation, never program iteration. The Python
snapshot adapter sorts exact scalars by the same (type name, value) key. -/
def before (left right : Constant) : Bool :=
  let a := (Data.scalar left).typeName
  let b := (Data.scalar right).typeName
  if a = b then (scalarCompare .lt left right).getD false else decide (a < b)

def canonical (items : List Constant) : List Constant := items.mergeSort before

/-- A scalar set has no distinct tied numeric values, so its maximum does not
depend on iteration order. Incomparable elements raise TypeError. -/
def maximum : List Constant → Except ExceptionObject Constant
  | [] => .error { typeName := "ValueError", args := [] }
  | first :: rest => Calls.maximumFrom first rest

/-- Minimum on an iterable, including the empty-input exception. -/
def minimum : List Constant → Except ExceptionObject Constant
  | [] => .error { typeName := "ValueError", args := [] }
  | first :: rest => Calls.minimumFrom first rest

theorem contains_insert_self (items : List Constant) (value : Constant) :
    contains (insert items value) value = true := by
  have reflexive : scalarCompare .eq value value = some true := by
    cases value <;> simp [scalarCompare, evalCmpOp]
  by_cases present : contains items value = true
  · simp [insert, present]
  · rw [insert, if_neg present]
    simp [contains, reflexive]

theorem insert_idempotent (items : List Constant) (value : Constant) :
    insert (insert items value) value = insert items value := by
  rw [insert, contains_insert_self]
  rfl

theorem maximumFrom_ints (items : List Int) (best : Int) :
    Calls.maximumFrom (.int best) (items.map Constant.int) =
      .ok (.int (items.foldl max best)) := by
  induction items generalizing best with
  | nil => rfl
  | cons head tail ih =>
      by_cases larger : best < head
      · simp [Calls.maximumFrom, scalarCompare, evalCmpOp, larger, ih,
          Int.max_eq_right (Int.le_of_lt larger)]
      · simp [Calls.maximumFrom, scalarCompare, evalCmpOp, larger, ih,
          Int.max_eq_left (Int.le_of_not_gt larger)]

theorem contains_ints (items : List Int) (value : Int) :
    contains (items.map Constant.int) (.int value) = decide (value ∈ items) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      change ((scalarCompare .eq (.int head) (.int value)).getD false ||
        contains (tail.map Constant.int) (.int value)) = _
      rw [ih]
      simp [scalarCompare, evalCmpOp, eq_comm]

theorem insert_ints (items : List Int) (value : Int) :
    insert (items.map Constant.int) (.int value) =
      (if value ∈ items then items else items ++ [value]).map Constant.int := by
  simp [insert, contains_ints]
  split <;> simp_all

end FormalSW.PyAst.ScalarSet
