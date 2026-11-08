import lang.py.FormalSW.HeapMapWork

/-! Scalar sets pay for worst-case key search and rebuilding storage on insertion.
The rebuilding allowance is paid on every insertion, so no hidden amortization
or expected hashing bound is needed. Key widths follow the arithmetic policy;
string keys retain their length costs even with fixed-cost integer arithmetic. -/
namespace FormalSW.PyAst.HeapCalls.SetWork
open PrimitiveWork

def width (arithmetic : Arithmetic) (items : List Constant) : Nat :=
  (items.map (scalarSize arithmetic)).foldl max 1

def insert (representation : MapRepresentation) (arithmetic : Arithmetic)
    (items : List Constant) (key : Constant) : Nat :=
  2 * mapLookup representation items.length (scalarSize arithmetic key + width arithmetic items) +
    (items.length + 1) * (width arithmetic items + 2)

/-- A full scan compares scalar keys and keeps one extremum. -/
def extremum (arithmetic : Arithmetic) (items : List Constant) : Nat :=
  (items.length + 1) * (2 * width arithmetic items + 1)

def lookup (representation : MapRepresentation) (arithmetic : Arithmetic)
    (heap : Mutable.Heap) (address : Nat) (key : Mutable.Value) : Option Nat :=
  match heap[address]?, key with
  | some (.set items), .scalar key =>
      some (mapLookup representation items.length (scalarSize arithmetic key + width arithmetic items))
  | _, _ => none

def operation (representation : MapRepresentation) (arithmetic : Arithmetic)
    (heap : Mutable.Heap) (op : Operation) (values : List Mutable.Value) : Option Nat :=
  match op, values with
  | .builtin .set, [] => some 1
  | .add address, [.scalar key] => match heap[address]? with
      | some (.set items) => some (insert representation arithmetic items key)
      | _ => none
  | .builtin .max, [.ref address] | .builtin .min, [.ref address] => match heap[address]? with
      | some (.set items) => some (extremum arithmetic items)
      | _ => none
  | _, _ => none

theorem width_ints (items : List Int) : width .word (items.map Constant.int) = 1 := by
  induction items with
  | nil => rfl
  | cons head tail ih => simpa [width, scalarSize, integer, List.foldl] using ih

theorem insert_ints (items : List Int) (key : Int) :
    insert .collisionChain .word (items.map Constant.int) (.int key) = 9 * (items.length + 1) := by
  simp [insert, width_ints, mapLookup, scalarSize, integer, Nat.mul_comm]
  omega

theorem membership_ints (heap : Mutable.Heap) (address : Nat) (items : List Int) (key : Int)
    (found : heap[address]? = some (.set (items.map Constant.int))) :
    lookup .collisionChain .word heap address (.scalar (.int key)) =
      some (3 * (items.length + 1)) := by
  simp [lookup, found, width_ints, mapLookup, scalarSize, integer, Nat.mul_comm]

theorem extremum_ints (items : List Int) :
    extremum .word (items.map Constant.int) = 3 * (items.length + 1) := by
  simp [extremum, width_ints, Nat.mul_comm]

end FormalSW.PyAst.HeapCalls.SetWork
