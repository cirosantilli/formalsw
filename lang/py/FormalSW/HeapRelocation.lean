import lang.py.FormalSW.RuntimeRelocation
import lang.py.FormalSW.IteratorCalls

/-! Runtime relocation for bound operations, identity, and implicit iterator dispatch. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- Locals retain references to corresponding cells, including captured environments. -/
def relocateEnv (rename : Nat → Nat) (env : Env) : Env :=
  fun name => (env name).map (relocateValue rename)

def relocateOperation (rename : Nat → Nat) : Operation → Operation
  | .method receiver args body => .method (relocateValue rename receiver) args body
  | .setField name value => .setField name (relocateValue rename value)
  | .setItem value => .setItem (relocateValue rename value)
  | .setSlice value => .setSlice (relocateValue rename value)
  | .append address => .append (rename address)
  | .extendList address => .extendList (rename address)
  | .updateSet address => .updateSet (rename address)
  | .pop address => .pop (rename address)
  | .count address => .count (rename address)
  | .sort address => .sort (rename address)
  | .sortReverse address => .sortReverse (rename address)
  | .add address => .add (rename address)
  | .dictionaryGet address => .dictionaryGet (rename address)
  | .dictionarySetDefault address => .dictionarySetDefault (rename address)
  | .dictionaryClear address => .dictionaryClear (rename address)
  | .comprehensionStore address => .comprehensionStore (rename address)
  | .sumGenerator element generators env start =>
      .sumGenerator element generators (relocateEnv rename env) start
  | .comprehension element generators env => .comprehension element generators (relocateEnv rename env)
  | .comprehensionTargets element generators env =>
      .comprehensionTargets element generators (relocateEnv rename env)
  | .setComprehension element generators env => .setComprehension element generators (relocateEnv rename env)
  | .dictionaryComprehension key value generators env =>
      .dictionaryComprehension key value generators (relocateEnv rename env)
  | .permutationStart target body otherwise following env =>
      .permutationStart target body otherwise following (relocateEnv rename env)
  | .combinationStart target body otherwise following env =>
      .combinationStart target body otherwise following (relocateEnv rename env)
  | .zipStart target body otherwise following env =>
      .zipStart target body otherwise following (relocateEnv rename env)
  | .sumGeneratorTargets element generators env start =>
      .sumGeneratorTargets element generators (relocateEnv rename env) start
  | .truthGenerator universal element generators env =>
      .truthGenerator universal element generators (relocateEnv rename env)
  | .extremumGenerator maximum fallback element generators env =>
      .extremumGenerator maximum fallback element generators (relocateEnv rename env)
  | .generatorCollect action element generators env =>
      .generatorCollect action element generators (relocateEnv rename env)
  | .nextGenerator fallback element generators env =>
      .nextGenerator fallback element generators (relocateEnv rename env)
  | .isDigit receiver => .isDigit (relocateValue rename receiver)
  | operation => operation

variable {logical physical : Mutable.Heap} {rename : Nat → Nat}

theorem relocateEnv_set (env : Env) (name : String) (value : Value) :
    relocateEnv rename (setLocal env name value) =
      setLocal (relocateEnv rename env) name (relocateValue rename value) := by
  funext query
  by_cases same : query = name <;> simp [relocateEnv, setLocal, same]

/-- Injective relocation retains identity comparisons, without invoking user equality. -/
theorem identity_relocates (layout : RuntimeLayout logical physical rename)
    (left right : Value) (leftInside : left.edge.Within logical.length)
    (rightInside : right.edge.Within logical.length) :
    identity (relocateValue rename left) (relocateValue rename right) physical =
      (identity left right logical).map (fun result => (result.1, physical)) := by
  cases left with
  | scalar a =>
    cases right with
    | ref b => simp [identity, relocateValue]
    | scalar b =>
      cases comparison : scalarIdentity a b <;>
        simp [identity, relocateValue, scalarResult, comparison, Mutable.unsupported]
  | ref a =>
    cases right with
    | scalar b => simp [identity, relocateValue]
    | ref b =>
      have same : (rename a == rename b) = (a == b) := by
        by_cases equal : a = b
        · simp [equal]
        · have different : rename a ≠ rename b := by
            intro merged
            exact equal (layout.injective a leftInside b rightInside merged)
          simp [beq_eq_false_iff_ne.mpr equal, beq_eq_false_iff_ne.mpr different]
      simp [identity, relocateValue, same]

/-- Relocation preserves class identity, missing slots, and unsupported bindings. -/
theorem lookup_relocates (layout : RuntimeLayout logical physical rename)
    (module : Module) (receiver : Value) (name : String)
    (inside : receiver.edge.Within logical.length) :
    ProtocolCalls.lookup module (relocateValue rename receiver) name physical =
      (ProtocolCalls.lookup module receiver name logical).map
        (fun result => (result.1.map (Option.map (relocateOperation rename)), physical)) := by
  cases receiver with
  | scalar value => simp [ProtocolCalls.lookup, relocateValue, Mutable.unsupported]
  | ref index =>
    have found : logical[index]? = some logical[index] := List.getElem?_eq_getElem inside
    have moved := layout.lookup index _ found
    cases object : logical[index] with
    | «instance» origin className fields | dataInstance origin className frozen declared fields =>
      simp only [object, relocateObject] at moved
      cases definition : module.findClass className with
      | none =>
        simp [ProtocolCalls.lookup, relocateValue, found, object, moved, instanceClass,
          definition, Mutable.unsupported]
      | some pair =>
        rcases pair with ⟨identity, body⟩
        by_cases nominal : identity = origin <;>
          simp [ProtocolCalls.lookup, relocateValue, found, object, moved, instanceClass,
            definition, nominal, Mutable.unsupported, Except.map, Option.map_map,
            Function.comp_def, relocateOperation]
    | list items | tuple items | bytearray bytes | set items | keySet items | dict entries | keyDict entries =>
      simp only [object, relocateObject] at moved
      simp [ProtocolCalls.lookup, relocateValue, found, object, moved, Mutable.unsupported]

/-- The next slot is the same method at the corresponding receiver, or absent on both sides. -/
theorem nextMethod_relocates (layout : RuntimeLayout logical physical rename)
    (module : Module) (receiver : Value) (inside : receiver.edge.Within logical.length) :
    ProtocolCalls.nextMethod module (relocateValue rename receiver) physical =
      (ProtocolCalls.nextMethod module receiver logical).map
        (fun result => (result.1.map (Option.map (relocateOperation rename)), physical)) := by
  cases receiver with
  | scalar value => simp [ProtocolCalls.nextMethod, relocateValue, Except.map]
  | ref index =>
    have found : logical[index]? = some logical[index] := List.getElem?_eq_getElem inside
    have moved := layout.lookup index _ found
    cases object : logical[index] with
    | «instance» origin className fields | dataInstance origin className frozen declared fields =>
      simp only [object, relocateObject] at moved
      simpa [ProtocolCalls.nextMethod, relocateValue, found, object, moved] using
        lookup_relocates layout module (.ref index) "__next__" inside
    | list items | tuple items | bytearray bytes | set items | keySet items | dict entries | keyDict entries =>
      simp only [object, relocateObject] at moved
      simp [ProtocolCalls.nextMethod, relocateValue, found, object, moved, Except.map]

theorem isInstance_relocates (layout : RuntimeLayout logical physical rename)
    (receiver : Value) (inside : receiver.edge.Within logical.length) :
    IteratorCalls.isInstance physical (relocateValue rename receiver) =
      IteratorCalls.isInstance logical receiver := by
  cases receiver with
  | scalar value => rfl
  | ref index =>
    have found : logical[index]? = some logical[index] := List.getElem?_eq_getElem inside
    have moved := layout.lookup index _ found
    cases object : logical[index] <;>
      simp [IteratorCalls.isInstance, relocateValue, relocateObject, found, object] at moved ⊢ <;>
      simp [moved]


private theorem lookup_keeps_heap (module : Module) (receiver : Value) (name : String)
    (heap after : Mutable.Heap) (outcome : Except ExceptionObject (Option Operation))
    (executed : ProtocolCalls.lookup module receiver name heap = some (outcome, after)) :
    after = heap := by
  cases receiver with
  | scalar value => simp [ProtocolCalls.lookup, Mutable.unsupported] at executed
  | ref index =>
    cases found : heap[index]? with
    | none => simp [ProtocolCalls.lookup, found, Mutable.unsupported] at executed
    | some object =>
      cases object with
      | «instance» origin className fields | dataInstance origin className frozen declared fields =>
        cases definition : module.findClass className with
        | none => simp [ProtocolCalls.lookup, found, instanceClass, definition, Mutable.unsupported] at executed
        | some pair =>
          rcases pair with ⟨identity, body⟩
          by_cases nominal : identity = origin <;>
            simp_all [ProtocolCalls.lookup, instanceClass, Mutable.unsupported]
      | list items | tuple items | bytearray bytes | set items | keySet items | dict entries | keyDict entries =>
        simp [ProtocolCalls.lookup, found, Mutable.unsupported] at executed

/-- Acquisition preserves its chosen __iter__ method and the missing-slot fallback boundary. -/
theorem iterMethod_relocates (layout : RuntimeLayout logical physical rename)
    (module : Module) (receiver : Value) (inside : receiver.edge.Within logical.length) :
    ProtocolCalls.iterMethod module (relocateValue rename receiver) physical =
      (ProtocolCalls.iterMethod module receiver logical).map
        (fun result => (result.1.map (relocateOperation rename), physical)) := by
  have iter := lookup_relocates layout module receiver "__iter__" inside
  have fallback := lookup_relocates layout module receiver "__getitem__" inside
  cases searched : ProtocolCalls.lookup module receiver "__iter__" logical with
  | none => simp [ProtocolCalls.iterMethod, Mutable.eval_bind, searched, iter]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have same := lookup_keeps_heap module receiver "__iter__" logical after outcome searched
    subst after
    cases outcome with
    | error error => simp [ProtocolCalls.iterMethod, Mutable.eval_bind, searched, iter, Except.map]
    | ok method =>
      cases method with
      | some operation => simp [ProtocolCalls.iterMethod, Mutable.eval_bind, searched, iter, Except.map]
      | none =>
        cases checked : ProtocolCalls.lookup module receiver "__getitem__" logical with
        | none => simp [ProtocolCalls.iterMethod, Mutable.eval_bind, searched, checked, iter, fallback, Except.map]
        | some pair =>
          rcases pair with ⟨outcome, after⟩
          have same := lookup_keeps_heap module receiver "__getitem__" logical after outcome checked
          subst after
          cases outcome with
          | error error =>
            simp [ProtocolCalls.iterMethod, Mutable.eval_bind, searched, checked, iter, fallback, Except.map]
          | ok method =>
            cases method <;> simp [ProtocolCalls.iterMethod, Mutable.eval_bind, searched, checked,
              iter, fallback, Except.map, Mutable.error, Mutable.unsupported]

end FormalSW.PyAst.HeapCalls.Relocation
