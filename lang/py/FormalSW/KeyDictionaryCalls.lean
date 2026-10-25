import lang.py.FormalSW.DictionaryCalls

/-! Proof rules for tuple-key dictionaries and eager default insertion. -/
namespace FormalSW.PyAst

namespace HashDict
@[simp] theorem lookup_nil (key : HashKey) : lookup ([] : List (Entry α)) key = none := rfl

@[simp] theorem lookup_cons (entry : Entry α) (rest : List (Entry α)) (key : HashKey) :
    lookup (entry :: rest) key =
      if HashKey.equal entry.1 key then some entry.2.2 else lookup rest key := by
  cases equal : HashKey.equal entry.1 key <;> simp [lookup, find?, equal]
end HashDict

namespace Mutable

theorem dictionarySetDefault_scalar (heap : Heap) (address : Nat) (entries : List (Constant × Value))
    (found : heap[address]? = some (.dict entries)) (key : Constant) (defaultValue : Value) :
    dictionarySetDefault address (.scalar key) defaultValue heap =
      some (.ok ((ScalarDict.lookup entries key).getD defaultValue),
        if (ScalarDict.lookup entries key).isSome then heap
        else heap.set address (.dict (ScalarDict.insert entries key defaultValue))) := by
  cases value : ScalarDict.lookup entries key <;>
    simp [dictionarySetDefault, found, value, Except.map]

theorem dictionarySetDefault_keyed (heap : Heap) (address : Nat) (entries : List (HashDict.Entry Value))
    (found : heap[address]? = some (.keyDict entries)) (key : Value) (hashed : HashKey)
    (hash : hashKey key heap = some (.ok hashed, heap)) (defaultValue : Value) :
    dictionarySetDefault address key defaultValue heap =
      some (.ok ((HashDict.lookup entries hashed).getD defaultValue),
        if (HashDict.lookup entries hashed).isSome then heap
        else heap.set address (.keyDict (HashDict.insert entries hashed key defaultValue))) := by
  cases value : HashDict.lookup entries hashed <;>
    simp [dictionarySetDefault, found, hash, value, Except.map]

theorem dictionarySetDefault_promote (heap : Heap) (address : Nat) (entries : List (Constant × Value))
    (found : heap[address]? = some (.dict entries)) (keyAddress : Nat) (hashed : HashKey)
    (hash : hashKey (.ref keyAddress) heap = some (.ok hashed, heap)) (defaultValue : Value) :
    dictionarySetDefault address (.ref keyAddress) defaultValue heap =
      some (.ok ((HashDict.lookup (promoteDictionary entries) hashed).getD defaultValue),
        if (HashDict.lookup (promoteDictionary entries) hashed).isSome then heap
        else heap.set address (.keyDict (HashDict.insert (promoteDictionary entries) hashed (.ref keyAddress) defaultValue))) := by
  cases value : HashDict.lookup (promoteDictionary entries) hashed <;>
    simp [dictionarySetDefault, found, hash, value, Except.map]

theorem dictionaryGet_keyed (heap : Heap) (address : Nat) (entries : List (HashDict.Entry Value))
    (found : heap[address]? = some (.keyDict entries)) (key : Value) (hashed : HashKey)
    (hash : hashKey key heap = some (.ok hashed, heap)) (defaultValue : Value) :
    dictionaryGet address key defaultValue heap =
      some (.ok ((HashDict.lookup entries hashed).getD defaultValue), heap) := by
  simp [dictionaryGet, found, hash, Except.map]
end Mutable

namespace HeapCalls.Evaluates
variable {globals : Mutable.Globals}

/-- Binding captures the dictionary address before any key or default argument runs. -/
theorem dictionary_setdefault
    (localName : ∀ name, base = .name name → env name ≠ none)
    (receiver : Evaluates (globals := globals) module env base heap (.ref address) afterReceiver)
    (bound : bindMethod module (.ref address) "setdefault" afterReceiver =
      some (.ok (.dictionarySetDefault address), afterReceiver))
    (arguments : Arguments (globals := globals) module env expressions afterReceiver values afterArguments)
    (operation : primitive (.dictionarySetDefault address) values afterArguments = some (.ok value, finalHeap)) :
    Evaluates (globals := globals) module env (.call (.attribute base "setdefault") expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr base env, .methodReceiver "setdefault" expressions env :: stack, heap⟩)
    (by cases base <;> simp_all [step, Option.isSome_iff_ne_none])
  apply (receiver anchors _).trans
  apply Reaches.next (following := argumentsState (.dictionarySetDefault address) env [] expressions stack afterReceiver)
    (by simp [step, run, bound])
  apply (arguments_reach arguments (.dictionarySetDefault address) [] anchors stack).trans
  exact .next (by simp [step, result, run, operation]) .refl

/-- The same get rule applies before and after promotion to tuple keys. -/
theorem dictionary_get_bound
    (localName : ∀ name, base = .name name → env name ≠ none)
    (receiver : Evaluates (globals := globals) module env base heap (.ref address) afterReceiver)
    (bound : bindMethod module (.ref address) "get" afterReceiver = some (.ok (.dictionaryGet address), afterReceiver))
    (arguments : Arguments (globals := globals) module env expressions afterReceiver values afterArguments)
    (operation : primitive (.dictionaryGet address) values afterArguments = some (.ok value, finalHeap)) :
    Evaluates (globals := globals) module env (.call (.attribute base "get") expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr base env, .methodReceiver "get" expressions env :: stack, heap⟩)
    (by cases base <;> simp_all [step, Option.isSome_iff_ne_none])
  apply (receiver anchors _).trans
  apply Reaches.next (following := argumentsState (.dictionaryGet address) env [] expressions stack afterReceiver)
    (by simp [step, run, bound])
  apply (arguments_reach arguments (.dictionaryGet address) [] anchors stack).trans
  exact .next (by simp [step, result, run, operation]) .refl
end HeapCalls.Evaluates
end FormalSW.PyAst
