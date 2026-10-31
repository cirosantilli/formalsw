import lang.py.FormalSW.DictionaryCalls

namespace FormalSW.PyAst.DictionaryConstructor

theorem construct_empty (heap : Heap) :
    construct [] heap = some (.ok (.ref heap.length), heap ++ [.dict []]) := by
  simp [construct, Mutable.allocateDict, Except.map]

/-- A fresh outer dictionary preserves every original key and value reference. -/
theorem construct_dict (heap : Heap) (address : Nat) (entries : List (Constant × Value))
    (found : heap[address]? = some (.dict entries)) :
    construct [.ref address] heap =
      some (.ok (.ref heap.length), heap ++ [.dict entries]) := by
  simp [construct, found, Mutable.allocateDict, Except.map]

/-- Tuple-key representatives and their cached keys survive without rehashing. -/
theorem construct_keyed (heap : Heap) (address : Nat) (entries : List (HashDict.Entry Value))
    (found : heap[address]? = some (.keyDict entries)) :
    construct [.ref address] heap =
      some (.ok (.ref heap.length), heap ++ [.keyDict entries]) := by
  simp [construct, found, Except.map]

theorem copy_preserves_object (heap : Heap) (object : Mutable.Object) (address : Nat)
    (present : address < heap.length) :
    (heap ++ [object])[address]? = heap[address]? :=
  List.getElem?_append_left present

theorem copy_address_fresh (heap : Heap) (address : Nat) (object : Mutable.Object)
    (found : heap[address]? = some object) : heap.length ≠ address :=
  Nat.ne_of_gt (List.getElem?_eq_some_iff.mp found).1

/-- Replacing the copy's bindings leaves every previously allocated object intact. -/
theorem copy_set_preserves_object (heap : Heap) (initial replacement : Mutable.Object)
    (address : Nat) (present : address < heap.length) :
    ((heap ++ [initial]).set heap.length replacement)[address]? = heap[address]? := by
  rw [List.getElem?_set_ne (Nat.ne_of_gt present)]
  exact copy_preserves_object heap initial address present

theorem iterable_dict (heap : Heap) (address : Nat) (entries : List (Constant × Value))
    (found : heap[address]? = some (.dict entries)) :
    iterable (.ref address) heap =
      some (.ok (entries.map fun entry => .scalar entry.1), heap) := by
  simp [iterable, found]

/-- Sequence construction retains the reached heap even if a later row raises. -/
theorem fromIterable_result (heap after : Heap) (value : Value) (rows : List Value)
    (outcome : Except ExceptionObject Unit)
    (iterated : iterable value (heap ++ [.dict []]) =
      some (.ok rows, heap ++ [.dict []]))
    (inserted : insertRows heap.length rows (heap ++ [.dict []]) = some (outcome, after)) :
    fromIterable value heap = some (outcome.map (fun _ => .ref heap.length), after) := by
  cases outcome <;>
    simp [fromIterable, Mutable.allocateDict, iterated, inserted, Except.map]

end FormalSW.PyAst.DictionaryConstructor

namespace FormalSW.PyAst.HeapCalls

theorem primitive_dict_constructor (values : List Value) :
    primitive (.builtin .dict) values = DictionaryConstructor.construct values := rfl

theorem primitive_dict_copy (heap : Heap) (address : Nat) (entries : List (Constant × Value))
    (found : heap[address]? = some (.dict entries)) :
    primitive (.builtin .dict) [.ref address] heap =
      some (.ok (.ref heap.length), heap ++ [.dict entries]) :=
  DictionaryConstructor.construct_dict heap address entries found

theorem primitive_keydict_copy (heap : Heap) (address : Nat) (entries : List (HashDict.Entry Value))
    (found : heap[address]? = some (.keyDict entries)) :
    primitive (.builtin .dict) [.ref address] heap =
      some (.ok (.ref heap.length), heap ++ [.keyDict entries]) :=
  DictionaryConstructor.construct_keyed heap address entries found

end FormalSW.PyAst.HeapCalls
