import lang.py.FormalSW.HeapCalls
import lang.py.FormalSW.PrimitiveWork

/-! Dictionary primitive tariffs for HeapCalls. The heap records Python-observable
entries; the representation parameter selects the target map's search cost, not
the cost of traversing that semantic list inside Lean. Scalar-key lookups account
for both map size and key-comparison work. Object-key protocols need separate rules. -/
namespace FormalSW.PyAst.HeapCalls.MapWork
open PrimitiveWork

def keyWork (arithmetic : Arithmetic) (entries : List (Constant × Mutable.Value)) (key : Constant) : Nat :=
  scalarSize arithmetic key +
    (entries.map fun entry => scalarSize arithmetic entry.1).foldl max 0

def lookup (representation : MapRepresentation) (arithmetic : Arithmetic)
    (heap : Mutable.Heap) (address : Nat) (key : Mutable.Value) : Option Nat :=
  match heap[address]?, key with
  | some (.dict entries), .scalar key =>
      some (mapLookup representation entries.length (keyWork arithmetic entries key))
  | _, _ => none

/-- No fallback: non-map primitives and unmodeled key protocols return `none`. -/
def operation (representation : MapRepresentation) (arithmetic : Arithmetic)
    (heap : Mutable.Heap) (op : Operation) (values : List Mutable.Value) : Option Nat :=
  match op, values with
  | .subscript, [.ref address, key]
  | .dictionaryGet address, [key]
  | .dictionaryGet address, [key, _]
  | .membership _, [key, .ref address] => lookup representation arithmetic heap address key
  | .setItem _, [.ref address, key] =>
      (lookup representation arithmetic heap address key).map (· + 1)
  | .dictionarySetDefault address, [key]
  | .dictionarySetDefault address, [key, _] =>
      (lookup representation arithmetic heap address key).map (fun work => 2 * work + 1)
  | _, _ => none

theorem subscript (representation : MapRepresentation) (arithmetic : Arithmetic)
    (heap : Mutable.Heap) (address : Nat) (entries : List (Constant × Mutable.Value)) (key : Constant)
    (found : heap[address]? = some (.dict entries)) :
    operation representation arithmetic heap .subscript [.ref address, .scalar key] =
      some (mapLookup representation entries.length (keyWork arithmetic entries key)) := by
  simp [operation, lookup, found]

theorem missing_key_protocol (representation : MapRepresentation) (arithmetic : Arithmetic)
    (heap : Mutable.Heap) (address keyAddress : Nat) :
    lookup representation arithmetic heap address (.ref keyAddress) = none := by
  simp only [lookup]
  split <;> first | contradiction | rfl

end FormalSW.PyAst.HeapCalls.MapWork
