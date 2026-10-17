import Std.Data.TreeMap

/-!
A model of Python's insertion-ordered `dict`, backed by Lean's size-balanced
binary search tree.  The list records Python's observable insertion order;
lookup, insertion, replacement, and deletion use the balanced tree.
-/

namespace FormalSW.Py.Builtin.Dict

universe u v

/-- A Python dictionary with insertion order and balanced-tree lookup. -/
structure Dict (α : Type u) (β : Type v)
    (cmp : α → α → Ordering := by exact compare) where
  tree : Std.TreeMap α β cmp
  order : List α

/-- Construct an empty dictionary. -/
def empty : Dict α β cmp := ⟨Std.TreeMap.empty, []⟩

/-- The number of key/value pairs. -/
def size (d : Dict α β cmp) : Nat := d.tree.size

/-- Test whether a key is present. -/
def contains (d : Dict α β cmp) (key : α) : Bool := d.tree.contains key

/-- Look up a key, returning `none` for a missing key. -/
def get? (d : Dict α β cmp) (key : α) : Option β := d.tree.get? key

/-- Return a value or the caller-provided default. -/
def getD (d : Dict α β cmp) (key : α) (default : β) : β :=
  d.tree.getD key default

/-- Insert or replace a key while retaining its original insertion position. -/
def set (d : Dict α β cmp) (key : α) (value : β) : Dict α β cmp :=
  let existed := d.tree.contains key
  { tree := d.tree.insert key value
    order := if existed then d.order else d.order ++ [key] }

/-- Remove a key.  Missing keys leave the dictionary unchanged. -/
def erase (d : Dict α β cmp) (key : α) : Dict α β cmp :=
  { tree := d.tree.erase key
    order := d.order.filter fun existing => cmp existing key != .eq }

/-- Remove every item. -/
def clear (_ : Dict α β cmp) : Dict α β cmp := empty

/-- A shallow copy. -/
def copy (d : Dict α β cmp) : Dict α β cmp := d

/-- Build a dictionary, with later duplicate keys replacing earlier values. -/
def ofList (entries : List (α × β)) : Dict α β cmp :=
  entries.foldl (fun d entry => set d entry.1 entry.2) empty

/-- `dict.fromkeys`: every key maps to the same supplied value. -/
def fromKeys (keys : List α) (value : β) : Dict α β cmp :=
  keys.foldl (fun d key => set d key value) empty

/-- Keys in Python's insertion order. -/
def keys (d : Dict α β cmp) : List α := d.order

/-- Items in Python's insertion order. -/
def items (d : Dict α β cmp) : List (α × β) :=
  d.order.filterMap fun key => (key, ·) <$> d.tree.get? key

/-- Values in Python's insertion order. -/
def values (d : Dict α β cmp) : List β := (items d).map Prod.snd

/-- Insert a default only when a key is absent, returning the resulting value. -/
def setDefault (d : Dict α β cmp) (key : α) (default : β) : β × Dict α β cmp :=
  match get? d key with
  | some value => (value, d)
  | none => (default, set d key default)

/-- Remove a key and return its value, or return `none` when absent. -/
def pop? (d : Dict α β cmp) (key : α) : Option β × Dict α β cmp :=
  (get? d key, erase d key)

/-- Remove the most recently inserted pair, matching Python's LIFO `popitem`. -/
def popItem? (d : Dict α β cmp) : Option (α × β) × Dict α β cmp :=
  match d.order.getLast? with
  | none => (none, d)
  | some key =>
      match get? d key with
      | none => (none, d)
      | some value => (some (key, value), erase d key)

/-- Update from key/value pairs, with the latter values taking priority. -/
def update (d : Dict α β cmp) (entries : List (α × β)) : Dict α β cmp :=
  entries.foldl (fun result entry => set result entry.1 entry.2) d

/-- Python's `d | other`; right-hand values take priority. -/
def union (d other : Dict α β cmp) : Dict α β cmp := update d (items other)

def equivalent [BEq β] (left right : Dict α β cmp) : Bool :=
  size left = size right && left.tree.all fun key value => get? right key == some value

/-- The bundled tree implementation is balanced for every dictionary value. -/
theorem tree_wellFormed (d : Dict α β cmp) :
    (letI : Ord α := ⟨cmp⟩; d.tree.inner.inner.WF) := by
  exact d.tree.inner.wf

end FormalSW.Py.Builtin.Dict
