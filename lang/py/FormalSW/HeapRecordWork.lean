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

/-- Only generated positional dataclass constructors are priced here.
User-written initializers still require their own source-execution rules. -/
def construct (module : Module) (name : String) (values : List Value) : Option Nat := do
  if (libraryFunction module name).isSome then none
  else
    let (_, body) ← module.findClass name
    if (findFunctionIn body "__init__").isSome then none
    else
      let (_, fields) ← dataclassFields body
      if fields.length = values.length then some (fields.length + values.length + 1) else none

end FormalSW.PyAst.HeapCalls.RecordWork
