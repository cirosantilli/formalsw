import lang.py.FormalSW.MutableGlobals

/-! Builtin set updates retain representatives and successful insertions before an error. -/
namespace FormalSW.PyAst.Mutable

/-- Snapshot builtin elements or dictionary keys. Custom iteration needs protocol dispatch. -/
def setSourceItems (source : Value) : Eval (List Value) := do
  match source with
  | .ref address => match (← get)[address]? with
      | some (.set items) => pure (items.map Value.scalar)
      | some (.keySet items) => pure (items.map Prod.snd)
      | some (.dict entries) => pure (entries.map fun entry => Value.scalar entry.1)
      | some (.keyDict entries) => pure (entries.map fun entry => entry.2.1)
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) | none => unsupported
      | _ => sequence source
  | _ => sequence source

/-- All argument expressions have already run. Sources are read and inserted in argument order. -/
def updateSet (address : Nat) : List Value → Eval Value
  | [] => pure (.scalar .none)
  | source :: rest => do
      let items ← setSourceItems source
      let _ ← items.mapM (addItem address)
      updateSet address rest

end FormalSW.PyAst.Mutable
