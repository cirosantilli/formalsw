import lang.py.FormalSW.MutableGlobals

/-! Singleton dictionary displays hash their key after evaluating the value.
The stored key and value retain their original references. -/
namespace FormalSW.PyAst.DictionaryDisplay

def singleton (key value : Mutable.Value) : Mutable.Eval Mutable.Value := do
  let hashed ← Mutable.hashKey key
  let address := (← get).length
  modify fun heap => heap ++ [.keyDict [(hashed, key, value)]]
  return .ref address

theorem singleton_result (heap : Mutable.Heap) (key value : Mutable.Value) (hashed : HashKey)
    (hash : Mutable.hashKey key heap = some (.ok hashed, heap)) :
    singleton key value heap = some (.ok (.ref heap.length), heap ++ [.keyDict [(hashed, key, value)]]) := by
  simp [singleton, hash, Except.map]

end FormalSW.PyAst.DictionaryDisplay
