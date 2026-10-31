import lang.py.FormalSW.MutableGlobals

/-! Dictionary construction retains key representatives, insertion order and shared
values. Custom mapping/iteration protocols and set traversal remain unsupported. -/
namespace FormalSW.PyAst.DictionaryConstructor

abbrev Value := Mutable.Value
abbrev Heap := Mutable.Heap
abbrev Eval := Mutable.Eval

/-- Dictionary rows iterate keys; sequences retain their original element references. -/
def iterable (value : Value) : Eval (List Value) := do
  if let .ref address := value then
    match (← get)[address]? with
    | some (.dict entries) => return entries.map fun entry => .scalar entry.1
    | some (.keyDict entries) => return entries.map fun entry => entry.2.1
    | some (.set _) | some (.keySet _) => Mutable.unsupported
    | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) | none => Mutable.unsupported
    | _ => Mutable.sequence value
  else
    Mutable.sequence value

def insertRow (address : Nat) (row : Value) : Eval Unit := do
  match ← iterable row with
  | [key, value] =>
      let _ ← Mutable.setItem (.ref address) key value
      pure ()
  | _ => Mutable.error "ValueError"

/-- Earlier rows stay inserted if a later row has bad length or an unhashable key. -/
def insertRows (address : Nat) : List Value → Eval Unit
  | [] => pure ()
  | row :: rest => do
      insertRow address row
      insertRows address rest

def fromIterable (value : Value) : Eval Value := do
  let address := (← get).length
  let _ ← Mutable.allocateDict []
  insertRows address (← iterable value)
  return .ref address

/-- Exact dictionaries take the shallow-copy path without rehashing their keys. -/
def construct : List Value → Eval Value
  | [] => Mutable.allocateDict []
  | [.ref address] => do
      match (← get)[address]? with
      | some (.dict entries) => Mutable.allocateDict entries
      | some (.keyDict entries) =>
          let destination := (← get).length
          modify fun heap => heap ++ [.keyDict entries]
          return .ref destination
      | none => Mutable.unsupported
      | some _ => fromIterable (.ref address)
  | [value] => fromIterable value
  | _ => Mutable.error "TypeError"

end FormalSW.PyAst.DictionaryConstructor
