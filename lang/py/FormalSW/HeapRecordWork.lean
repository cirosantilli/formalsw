import lang.py.FormalSW.HeapCalls

/-! Stored record fields use a conservative linear name search. Values and
compiled field names are retained by reference when constructing a record. -/
namespace FormalSW.PyAst.HeapCalls.RecordWork

/-- Every possible field-name comparison is charged, even if lookup stops early. -/
def lookup (name : String) (fields : List (String × Value)) : Nat :=
  (fields.map fun field => field.1.length + name.length + 1).sum + 1

def field (heap : Heap) (receiver : Value) (name : String) : Option Nat := do
  if name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__" then none
  else
    let .ref address := receiver | none
    let fields ← match heap[address]? with
      | some (.instance _ _ fields) | some (.dataInstance _ _ _ _ fields) => some fields
      | _ => none
    let _ ← fields.lookup name
    return lookup name fields

/-- Binding checks the live fields before retaining the compiled method.
Compiled class and method resolution have fixed overhead. -/
def method (module : Module) (heap : Heap) (receiver : Value) (name : String) : Option Nat := do
  let .ref address := receiver | none
  let fields ← match heap[address]? with
    | some (.instance _ _ fields) | some (.dataInstance _ _ _ _ fields) => some fields
    | _ => none
  let (.ok (.method _ _ _), _) ← bindMethod module receiver name heap | none
  return lookup name fields

/-- Ordinary field writes pay for name comparisons and rebuilding the field
spine. Assigning a reference does not copy the referenced object. -/
def write (heap : Heap) (receiver : Value) (name : String) : Option Nat := do
  if name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__" then none
  else
    let .ref address := receiver | none
    let fields ← match heap[address]? with
      | some (.instance _ _ fields) | some (.dataInstance _ _ false _ fields) => some fields
      | _ => none
    return lookup name fields + fields.length + 1

/-- Ordinary construction prices allocation and argument binding here; the
initializer body executes separately. Dataclass field copying is charged here. -/
def construct (module : Module) (name : String) (values : List Value) : Option Nat := do
  if (libraryFunction module name).isSome then none
  else
    let (_, body) ← module.findClass name
    match findFunctionIn body "__init__" with
    | some (args, _) => some (values.length + args.length + 2)
    | none =>
        let (_, fields) ← dataclassFields body
        if fields.length = values.length then some (fields.length + values.length + 1) else none

end FormalSW.PyAst.HeapCalls.RecordWork
