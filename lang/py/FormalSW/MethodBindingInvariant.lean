import lang.py.FormalSW.MachineExpressionInvariant

/-! Binding modeled methods retains bounded receivers and address-free source bodies. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- Bound methods contain no hidden runtime addresses in their source bodies. -/
def BoundMethodWithin (limit : Nat) (operation : Operation) : Prop :=
  OperationWithin limit operation ∧
    ∀ rename, relocateRuntimeOperation rename operation = relocateOperation rename operation

theorem BoundMethodWithin.method (limit : Nat) (receiver : Value) (args : List Arg) (body : List Stmt)
    (inside : receiver.edge.Within limit) (source : ∀ statement ∈ body, StmtWithin 0 statement) :
    BoundMethodWithin limit (.method receiver args body) := by
  refine ⟨⟨inside, fun statement member => (source statement member).mono (Nat.zero_le _)⟩, ?_⟩
  intro rename
  simp only [relocateRuntimeOperation, relocateOperation, relocateBody_source rename body source]

theorem bindMethod_scalar_within (module : Module) (heap after : Mutable.Heap)
    (value : Constant) (name : String) (operation : Operation)
    (ordinary : name ≠ "$formalsw.sort.reverse")
    (executed : bindMethod module (.scalar value) name heap = some (.ok operation, after)) :
    BoundMethodWithin heap.length operation := by
  by_cases isdigitName : name = "isdigit"
  · subst name
    cases value <;> simp [bindMethod, Mutable.error] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨by trivial, fun _ => rfl⟩
  by_cases upperName : name = "upper"
  · subst name
    cases value <;> simp [bindMethod, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨by trivial, fun _ => rfl⟩
  by_cases stripName : name = "strip"
  · subst name
    cases value <;> simp [bindMethod, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨by trivial, fun _ => rfl⟩
  by_cases splitName : name = "split"
  · subst name
    cases value <;> simp [bindMethod, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨by trivial, fun _ => rfl⟩
  by_cases replaceName : name = "replace"
  · subst name
    cases value <;> simp [bindMethod, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨by trivial, fun _ => rfl⟩
  by_cases zfillName : name = "zfill"
  · subst name
    cases value <;> simp [bindMethod, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨by trivial, fun _ => rfl⟩
  by_cases joinName : name = "join"
  · subst name
    cases value <;> simp [bindMethod, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨by trivial, fun _ => rfl⟩
  by_cases countName : name = "count"
  · subst name
    cases value <;> simp [bindMethod, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨by trivial, fun _ => rfl⟩
  by_cases appendName : name = "append"
  · subst name
    cases value <;> simp [bindMethod, Mutable.error] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨by trivial, fun _ => rfl⟩
  by_cases addName : name = "add"
  · subst name
    cases value <;> simp [bindMethod, Mutable.error] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨by trivial, fun _ => rfl⟩
  by_cases getName : name = "get"
  · subst name
    cases value <;> simp [bindMethod, Mutable.error] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨by trivial, fun _ => rfl⟩
  by_cases setdefaultName : name = "setdefault"
  · subst name
    cases value <;> simp [bindMethod, Mutable.error] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨by trivial, fun _ => rfl⟩
  by_cases popName : name = "pop"
  · subst name
    cases value <;> simp [bindMethod, Mutable.error] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨by trivial, fun _ => rfl⟩
  by_cases sortName : name = "sort"
  · subst name
    cases value <;> simp [bindMethod, Mutable.error] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨by trivial, fun _ => rfl⟩
  simp [bindMethod, ordinary, isdigitName, upperName, stripName, splitName, replaceName, zfillName, joinName, countName, appendName, addName, getName, setdefaultName, popName, sortName, Mutable.unsupported] at executed

set_option maxHeartbeats 400000 in
theorem bindMethod_builtin_within (module : Module) (heap after : Mutable.Heap)
    (address : Nat) (object : Mutable.Object) (name : String) (operation : Operation)
    (found : heap[address]? = some object) (inside : address < heap.length)
    (builtin : match object with | .instance _ _ _ | .dataInstance _ _ _ _ _ => False | _ => True)
    (ordinary : name ≠ "$formalsw.sort.reverse")
    (executed : bindMethod module (.ref address) name heap = some (.ok operation, after)) :
    BoundMethodWithin heap.length operation := by
  by_cases sortName : name = "sort"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  by_cases appendName : name = "append"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  by_cases extendName : name = "extend"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  by_cases updateName : name = "update"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  by_cases popName : name = "pop"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  by_cases countName : name = "count"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  by_cases addName : name = "add"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  by_cases getName : name = "get"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  by_cases setdefaultName : name = "setdefault"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  by_cases clearName : name = "clear"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  by_cases isdigitName : name = "isdigit"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  by_cases upperName : name = "upper"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  by_cases stripName : name = "strip"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  by_cases splitName : name = "split"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  by_cases zfillName : name = "zfill"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  by_cases replaceName : name = "replace"
  · subst name
    cases object <;> try contradiction
    all_goals simp [bindMethod, found, Mutable.error, Mutable.unsupported] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩; exact ⟨inside, fun _ => rfl⟩
  cases object <;> try contradiction
  all_goals simp [bindMethod, found, ordinary, sortName, appendName, extendName, updateName, popName, countName, addName, getName, setdefaultName, clearName, isdigitName, upperName, stripName, splitName, zfillName, replaceName, Mutable.unsupported] at executed

theorem bindMethod_ordinary_within (module : Module) (heap after : Mutable.Heap)
    (receiver : Value) (name : String) (operation : Operation)
    (source : ∀ statement ∈ module.body, StmtWithin 0 statement)
    (inside : receiver.edge.Within heap.length) (ordinary : name ≠ "$formalsw.sort.reverse")
    (executed : bindMethod module receiver name heap = some (.ok operation, after)) :
    BoundMethodWithin heap.length operation := by
  cases receiver with
  | scalar value => exact bindMethod_scalar_within module heap after value name operation ordinary executed
  | ref address =>
    have found := List.getElem?_eq_getElem inside
    cases object : heap[address] with
    | «instance» origin className fields | dataInstance origin className frozen declared fields =>
      cases definition : module.findClass className with
      | none => simp [bindMethod, ordinary, found, object, instanceClass, definition, Mutable.unsupported] at executed
      | some pair =>
        rcases pair with ⟨identity, body⟩
        by_cases nominal : identity = origin
        · by_cases special : name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__"
          · simp [bindMethod, ordinary, found, object, instanceClass, definition, nominal, special, Mutable.unsupported] at executed
          · cases field : fields.lookup name with
            | some value =>
              simp [bindMethod, ordinary, found, object, instanceClass, definition, nominal, special, field] at executed
              rcases executed with ⟨rfl, rfl⟩
              exact ⟨by trivial, fun _ => rfl⟩
            | none =>
              cases method : findFunctionIn body name with
              | none =>
                by_cases missing : ['_', '_'] <+: name.toList <;>
                  simp [bindMethod, ordinary, found, object, instanceClass, definition, nominal, special,
                    field, method, missing, Mutable.unsupported, Mutable.error] at executed
              | some pair =>
                rcases pair with ⟨args, methodBody⟩
                simp [bindMethod, ordinary, found, object, instanceClass, definition, nominal, special, field, method] at executed
                rcases executed with ⟨rfl, rfl⟩
                exact BoundMethodWithin.method _ _ _ _ inside
                  (findFunctionIn_within 0 body name args methodBody
                    (findClass_within 0 module className identity body source definition) method)
        · simp [bindMethod, ordinary, found, object, instanceClass, definition, nominal, Mutable.unsupported] at executed
    | list items | tuple items | bytearray bytes | set items | keySet items | dict entries | keyDict entries =>
      exact bindMethod_builtin_within module heap after address _ name operation
        found inside (by simp [object]) ordinary executed

end FormalSW.PyAst.HeapCalls.Relocation
