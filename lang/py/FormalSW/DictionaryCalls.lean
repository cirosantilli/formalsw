import lang.py.FormalSW.HeapCalls

/-! Compositional rules for scalar-key dictionary displays and lookups. -/
namespace FormalSW.PyAst

namespace Mutable

theorem dictionaryGet_scalar (heap : Heap) (address : Nat) (entries : List (Constant × Value))
    (found : heap[address]? = some (.dict entries)) (key : Constant) (defaultValue : Value) :
    dictionaryGet address (.scalar key) defaultValue heap =
      some (.ok ((ScalarDict.lookup entries key).getD defaultValue), heap) := by
  simp [dictionaryGet, dictionaryKey, found]

theorem getItem_dictionary (heap : Heap) (address : Nat) (entries : List (Constant × Value))
    (found : heap[address]? = some (.dict entries)) (key : Constant)
    (present : ScalarDict.lookup entries key = some value) :
    getItem (.ref address) (.scalar key) heap = some (.ok value, heap) := by
  simp [getItem, dictionaryKey, found, present]

theorem setItem_dictionary (heap : Heap) (address : Nat) (entries : List (Constant × Value))
    (found : heap[address]? = some (.dict entries)) (key : Constant) (value : Value) :
    setItem (.ref address) (.scalar key) value heap =
      some (.ok (.scalar .none), heap.set address (.dict (ScalarDict.insert entries key value))) := by
  simp [setItem, dictionaryKey, found, Except.map]

end Mutable

namespace HeapCalls.Evaluates

variable {globals : Mutable.Globals}


/-- Each key precedes its value; effects flow through all remaining entries. -/
inductive DictionaryEntries (module : Module) (env : Env) :
    List (Expr × Expr) → List (Constant × Value) → Heap → List (Constant × Value) → Heap →
      (globals : Mutable.Globals := []) → Prop where
  | nil {globals : Mutable.Globals} : DictionaryEntries (globals := globals) module env [] entries heap entries heap
  | cons {globals : Mutable.Globals} : Evaluates (globals := globals) module env keyExpr heap (.scalar key) afterKey →
      Evaluates (globals := globals) module env valueExpr afterKey value afterValue →
      DictionaryEntries (globals := globals) module env rest (ScalarDict.insert entries key value) afterValue finalEntries finalHeap →
      DictionaryEntries (globals := globals) module env ((keyExpr, valueExpr) :: rest) entries heap finalEntries finalHeap

theorem DictionaryEntries.reach
    (h : DictionaryEntries (globals := globals) module env expressions entries heap finalEntries finalHeap)
    (anchors : Nat) (stack : List Frame) :
    Reaches (globals := globals) module anchors ⟨.dictionary expressions entries env, stack, heap⟩
      ⟨.value (.ref finalHeap.length), stack, finalHeap ++ [.dict finalEntries]⟩ := by
  induction h with
  | nil => exact .next (by simp [step, result, run, Mutable.allocateDict, Except.map]) .refl
  | cons key value rest ih =>
      exact .next rfl ((key anchors _).trans (.next rfl ((value anchors _).trans (.next rfl ih))))

theorem dictionary (entries : DictionaryEntries (globals := globals) module env expressions [] heap finalEntries finalHeap) :
    Evaluates (globals := globals) module env (.dict expressions) heap (.ref finalHeap.length) (finalHeap ++ [.dict finalEntries]) :=
  fun anchors stack => .next rfl (entries.reach anchors stack)

/-- Constant tables use the same insertion semantics, including duplicate keys. -/
theorem DictionaryEntries.constants (entries : List (Constant × Constant))
    (initial : List (Constant × Value)) :
    DictionaryEntries (globals := globals) module env (entries.map fun (key, value) => (.constant key, .constant value))
      initial heap (entries.foldl (fun table (key, value) => ScalarDict.insert table key (.scalar value)) initial) heap := by
  induction entries generalizing initial with
  | nil => exact .nil
  | cons entry rest ih => exact .cons constant constant (ih _)

theorem dictionary_constants (entries : List (Constant × Constant)) :
    Evaluates (globals := globals) module env (.dict (entries.map fun (key, value) => (.constant key, .constant value)))
      heap (.ref heap.length)
      (heap ++ [.dict (entries.foldl (fun table (key, value) => ScalarDict.insert table key (.scalar value)) [])]) :=
  dictionary (DictionaryEntries.constants entries [])

/-- Capture the receiver before evaluating the default, then read its current contents. -/
theorem dictionary_get
    (localName : ∀ name, base = .name name → env name ≠ none)
    (receiver : Evaluates (globals := globals) module env base heap (.ref address) afterReceiver)
    (found : afterReceiver[address]? = some (.dict entries))
    (arguments : Arguments (globals := globals) module env expressions afterReceiver values afterArguments)
    (operation : primitive (.dictionaryGet address) values afterArguments = some (.ok value, finalHeap)) :
    Evaluates (globals := globals) module env (.call (.attribute base "get") expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr base env, .methodReceiver "get" expressions env :: stack, heap⟩)
    (by cases base <;> simp_all [step, Option.isSome_iff_ne_none])
  apply (receiver anchors _).trans
  apply Reaches.next (following := argumentsState (.dictionaryGet address) env [] expressions stack afterReceiver)
    (by simp [step, run, bindMethod, found])
  apply (arguments_reach arguments (.dictionaryGet address) [] anchors stack).trans
  exact .next (by simp [step, result, run, operation]) .refl

end HeapCalls.Evaluates
end FormalSW.PyAst
