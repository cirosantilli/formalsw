import Std.Data.TreeSet

/-!
Models of Python's `set` and `frozenset`.  Both use Lean's size-balanced
binary search tree; mutating Python operations are represented as pure
functions returning the updated tree.
-/

namespace CleanXY.Py.Builtin.Set

universe u

/-- Shared balanced-BST representation for mutable and frozen Python sets. -/
abbrev Set (α : Type u) (cmp : α → α → Ordering := by exact compare) :=
  Std.TreeSet α cmp

/-- Python's immutable set has the same extensional representation. -/
abbrev FrozenSet (α : Type u) (cmp : α → α → Ordering := by exact compare) :=
  Std.TreeSet α cmp

def empty : Set α cmp := Std.TreeSet.empty
def ofList (values : List α) : Set α cmp := Std.TreeSet.ofList values cmp
def size (s : Set α cmp) : Nat := s.size
def contains (s : Set α cmp) (value : α) : Bool := s.contains value
def insert (s : Set α cmp) (value : α) : Set α cmp := s.insert value
def erase (s : Set α cmp) (value : α) : Set α cmp := s.erase value
def add (s : Set α cmp) (value : α) : Set α cmp := insert s value
def discard (s : Set α cmp) (value : α) : Set α cmp := erase s value
def remove (s : Set α cmp) (value : α) : Option (Set α cmp) :=
  if contains s value then some (erase s value) else none
def clear (_ : Set α cmp) : Set α cmp := empty
def copy (s : Set α cmp) : Set α cmp := s
def toList (s : Set α cmp) : List α := s.toList

/-- True when the two sets have no common element. -/
def isDisjoint (left right : Set α cmp) : Bool :=
  left.all fun value => !right.contains value

/-- Non-strict subset comparison. -/
def isSubset (left right : Set α cmp) : Bool :=
  left.all fun value => right.contains value

/-- Strict subset comparison. -/
def isProperSubset (left right : Set α cmp) : Bool :=
  isSubset left right && left.size < right.size

def isSuperset (left right : Set α cmp) : Bool := isSubset right left
def isProperSuperset (left right : Set α cmp) : Bool := isProperSubset right left

def union (left right : Set α cmp) : Set α cmp := left.union right
def intersection (left right : Set α cmp) : Set α cmp := left.inter right
def difference (left right : Set α cmp) : Set α cmp := left.diff right

/-- Elements occurring in exactly one operand. -/
def symmetricDifference (left right : Set α cmp) : Set α cmp :=
  (left.diff right).union (right.diff left)

/-- The mutable update operations return their modified receiver. -/
def update (left right : Set α cmp) : Set α cmp := union left right
def intersectionUpdate (left right : Set α cmp) : Set α cmp := intersection left right
def differenceUpdate (left right : Set α cmp) : Set α cmp := difference left right
def symmetricDifferenceUpdate (left right : Set α cmp) : Set α cmp :=
  symmetricDifference left right

def equivalent (left right : Set α cmp) : Bool :=
  left.size = right.size && isSubset left right

/-- Deterministically remove the least element; Python permits any element. -/
def pop? (s : Set α cmp) : Option α × Set α cmp :=
  match s.toList.head? with
  | none => (none, s)
  | some value => (some value, s.erase value)

/-- Every modeled set carries the balanced-tree well-formedness proof. -/
theorem tree_wellFormed (s : Set α cmp) :
    (letI : Ord α := ⟨cmp⟩; s.inner.inner.inner.WF) := by
  exact s.inner.inner.wf

end CleanXY.Py.Builtin.Set
