import lang.py.builtin.type.sequence

/-! Python tuples: immutable, heterogeneous sequences represented extensionally as lists. -/

namespace FormalSW.Py.Builtin.Tuple

abbrev Tuple (α : Type u) := List α

def empty : Tuple α := []
def ofIterable (values : List α) : Tuple α := values
def size (values : Tuple α) : Nat := values.length
def get? (values : Tuple α) (index : Int) : Option α := Sequence.get? values index
def concat (left right : Tuple α) : Tuple α := left ++ right
def repeated (values : Tuple α) (count : Int) : Tuple α := Sequence.repeated values count
def count [BEq α] (values : Tuple α) (needle : α) : Nat := Sequence.count values needle
def index? [BEq α] (values : Tuple α) (needle : α) : Option Nat :=
  Sequence.index? values needle

end FormalSW.Py.Builtin.Tuple
