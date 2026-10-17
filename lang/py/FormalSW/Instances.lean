import lang.py.FormalSW.MutableGlobals

/-! Ordered instance dictionaries for statically defined plain Python classes.
Fields hold shared references, including references back to the instance itself.
Class descriptors and method binding are handled separately from stored fields. -/
namespace FormalSW.PyAst.Mutable

/-- Updating an existing field retains its position in the instance dictionary. -/
def putField : List (String × Value) → String → Value → List (String × Value)
  | [], name, value => [(name, value)]
  | (key, old) :: fields, name, value =>
      if key = name then (key, value) :: fields
      else (key, old) :: putField fields name value

theorem putField_lookup (fields : List (String × Value)) (name : String) (value : Value) :
    (putField fields name value).lookup name = some value := by
  induction fields with
  | nil => simp [putField]
  | cons field fields ih =>
      rcases field with ⟨key, old⟩
      by_cases same : key = name
      · subst key; simp [putField]
      · simp [putField, List.lookup, same, ih, beq_eq_false_iff_ne.mpr (Ne.symm same)]

theorem putField_lookup_other (fields : List (String × Value)) (name other : String) (value : Value)
    (different : other ≠ name) :
    (putField fields name value).lookup other = fields.lookup other := by
  induction fields with
  | nil => simp [putField, different]
  | cons field fields ih =>
      rcases field with ⟨key, old⟩
      by_cases same : key = name
      · subst key; simp [putField, List.lookup, beq_eq_false_iff_ne.mpr different]
      · simp [putField, List.lookup, same, ih]

/-- Allocation never changes any existing object or its address. -/
def allocateInstance (origin name : String) : Eval Value := do
  let heap ← get
  set (heap ++ [.instance origin name []])
  return .ref heap.length

/-- Dataclass initialization stores the positional fields without a user setter. -/
def allocateDataclass (origin name : String) (frozen : Bool) (declared : List String)
    (values : List Value) : Eval Value := do
  if declared.length ≠ values.length then error "TypeError"
  else
    let heap ← get
    set (heap ++ [.dataInstance origin name frozen declared (declared.zip values)])
    return .ref heap.length

/-- Read stored fields only; the caller resolves methods when the field is absent. -/
def instanceData (value : Value) : Eval (String × String × List (String × Value)) := do
  match value with
  | .scalar _ => error "AttributeError"
  | .ref address => match (← get)[address]? with
      | some (.instance origin name fields) | some (.dataInstance origin name _ _ fields) =>
          return (origin, name, fields)
      | some _ => error "AttributeError"
      | none => unsupported

def readField (receiver : Value) (name : String) : Eval Value := do
  if name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__" then unsupported
  else
    let (_, _, fields) ← instanceData receiver
    match fields.lookup name with
    | some value => return value
    | none => error "AttributeError"

def writeField (receiver : Value) (name : String) (value : Value) : Eval Value := do
  if name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__" then unsupported
  else
    let (origin, className, fields) ← instanceData receiver
    match receiver with
    | .ref address =>
        match (← get)[address]? with
        | some (.dataInstance _ _ frozen declared _) =>
            if frozen then error "FrozenInstanceError"
            else
              modify fun heap => heap.set address
                (.dataInstance origin className frozen declared (putField fields name value))
              return .scalar .none
        | _ =>
            modify fun heap => heap.set address (.instance origin className (putField fields name value))
            return .scalar .none
    | .scalar _ => error "AttributeError"

theorem allocateInstance_result (origin name : String) (heap : Heap) :
    allocateInstance origin name heap =
      some (.ok (.ref heap.length), heap ++ [.instance origin name []]) := rfl

theorem allocateDataclass_result (origin name : String) (frozen : Bool)
    (declared : List String) (values : List Value) (heap : Heap)
    (arity : declared.length = values.length) :
    allocateDataclass origin name frozen declared values heap =
      some (.ok (.ref heap.length), heap ++ [.dataInstance origin name frozen declared (declared.zip values)]) := by
  simp [allocateDataclass, arity, Except.map]

theorem writeField_frozen
    (found : heap[address]? = some (.dataInstance origin className true declared fields))
    (ordinary : name ≠ "__class__" ∧ name ≠ "__dict__" ∧ name ≠ "__weakref__") :
    writeField (.ref address) name value heap =
      some (.error {typeName := "FrozenInstanceError", args := []}, heap) := by
  simp [writeField, instanceData, found, ordinary.1, ordinary.2.1, ordinary.2.2, error]

theorem readField_result
    (found : heap[address]? = some (.instance origin className fields))
    (ordinary : name ≠ "__class__" ∧ name ≠ "__dict__" ∧ name ≠ "__weakref__")
    (field : fields.lookup name = some value) :
    readField (.ref address) name heap = some (.ok value, heap) := by
  simp [readField, instanceData, found, ordinary.1, ordinary.2.1, ordinary.2.2, field]

theorem writeField_result
    (found : heap[address]? = some (.instance origin className fields))
    (ordinary : name ≠ "__class__" ∧ name ≠ "__dict__" ∧ name ≠ "__weakref__") :
    writeField (.ref address) name value heap = some (.ok (.scalar .none),
      heap.set address (.instance origin className (putField fields name value))) := by
  simp [writeField, instanceData, found, ordinary.1, ordinary.2.1, ordinary.2.2, Except.map]

end FormalSW.PyAst.Mutable
