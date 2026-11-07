import lang.py.FormalSW.DictionaryCalls
import lang.py.FormalSW.HeapRuntimeCostBuffers

/-! Scalar dictionary displays and get calls pay for the current table size and
key widths. Constant displays retain Python's duplicate-key insertion semantics. -/
namespace FormalSW.PyAst.HeapCalls.Runtime
open PrimitiveWork

/-- Contents of a constant display, including replacement of duplicate keys. -/
def dictionaryContents (pairs : List (Constant × Constant)) : List (Constant × Value) :=
  pairs.foldl (fun table (key, value) => ScalarDict.insert table key (.scalar value)) []

/-- Each pair evaluates its key and value, searches the growing table and writes
the value reference. The final allocation copies the completed entry references. -/
def dictionaryEntriesBudget (arithmetic : Arithmetic) :
    List (Constant × Constant) → List (Constant × Value) → Nat
  | [], entries => entries.length + 1
  | (key, value) :: rest, entries =>
      mapLookup .collisionChain entries.length (MapWork.keyWork arithmetic entries key) + 6 +
        dictionaryEntriesBudget arithmetic rest (ScalarDict.insert entries key (.scalar value))

/-- The actual display expression, its entry frames and its final allocation.
Word arithmetic still charges string-key widths and collision-chain searches. -/
def dictionaryLiteralBudget (pairs : List (Constant × Constant))
    (arithmetic : Arithmetic := .word) : Nat :=
  1 + dictionaryEntriesBudget arithmetic pairs []

theorem dictionary_constants_reach (pairs : List (Constant × Constant))
    (entries : List (Constant × Value)) :
    Reaches arithmetic module anchors
      ⟨.dictionary (pairs.map fun (key, value) => (.constant key, .constant value)) entries env,
        stack, heap⟩ (dictionaryEntriesBudget arithmetic pairs entries)
      ⟨.value (.ref heap.length), stack,
        heap ++ [.dict (pairs.foldl
          (fun table (key, value) => ScalarDict.insert table key (.scalar value)) entries)]⟩ := by
  induction pairs generalizing entries with
  | nil =>
      apply RuntimeCost.Amortized.Reaches.next (amount := entries.length + 1)
      · simp [step, result, run, Mutable.allocateDict, Except.map]
      · rfl
      · simp [dictionaryEntriesBudget, potential, heapPotential, objectPotential]
  | cons pair rest ih =>
      obtain ⟨key, value⟩ := pair
      have first : Reaches arithmetic module anchors
          ⟨.dictionary ((.constant key, .constant value) ::
            rest.map (fun (key, value) => (.constant key, .constant value))) entries env, stack, heap⟩ 1
          ⟨.expr (.constant key) env, .dictionaryKey (.constant value)
            (rest.map fun (key, value) => (.constant key, .constant value)) entries env :: stack, heap⟩ :=
        advance rfl rfl rfl
      have next : Reaches arithmetic module anchors
          ⟨.value (.scalar key), .dictionaryKey (.constant value)
            (rest.map fun (key, value) => (.constant key, .constant value)) entries env :: stack, heap⟩ 1
          ⟨.expr (.constant value) env, .dictionaryValue key
            (rest.map fun (key, value) => (.constant key, .constant value)) entries env :: stack, heap⟩ :=
        advance rfl rfl rfl
      have inserted : Reaches arithmetic module anchors
          ⟨.value (.scalar value), .dictionaryValue key
            (rest.map fun (key, value) => (.constant key, .constant value)) entries env :: stack, heap⟩
          (mapLookup .collisionChain entries.length (MapWork.keyWork arithmetic entries key) + 2)
          ⟨.dictionary (rest.map fun (key, value) => (.constant key, .constant value))
            (ScalarDict.insert entries key (.scalar value)) env, stack, heap⟩ := advance rfl rfl rfl
      exact (((((first.trans (EvaluatesIn.constant anchors _)).trans next).trans
        (EvaluatesIn.constant anchors _)).trans inserted).trans (ih _)).mono
          (by simp only [dictionaryEntriesBudget]; omega)

namespace EvaluatesIn

theorem dictionary_constants (pairs : List (Constant × Constant)) :
    EvaluatesIn arithmetic module env
      (.dict (pairs.map fun (key, value) => (.constant key, .constant value)))
      heap (dictionaryLiteralBudget pairs arithmetic) (.ref heap.length)
      (heap ++ [.dict (dictionaryContents pairs)]) := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.expr (.dict (pairs.map fun (key, value) => (.constant key, .constant value))) env, stack, heap⟩ 1
      ⟨.dictionary (pairs.map fun (key, value) => (.constant key, .constant value)) [] env, stack, heap⟩ :=
    advance rfl rfl rfl
  exact first.trans (dictionary_constants_reach pairs [])

/-- Bind before evaluating arguments, then price the live dictionary. The result
proof may choose a present value or the supplied (or implicit None) default. -/
theorem dictionary_get
    (localName : ∀ name, base = .name name → env name ≠ none)
    (receiver : EvaluatesIn arithmetic module env base heap cr (.ref address) afterReceiver)
    (found : afterReceiver[address]? = some (.dict entries))
    (arguments : ArgumentsIn arithmetic module env 0 expressions afterReceiver ca values afterArguments)
    (current : afterArguments[address]? = some (.dict currentEntries))
    (arity : values = [.scalar key] ∨ ∃ fallback, values = [.scalar key, fallback])
    (evaluated : primitive (.dictionaryGet address) values afterArguments =
      some (.ok value, afterArguments)) :
    EvaluatesIn arithmetic module env (.call (.attribute base "get") expressions) heap
      (cr + ca + mapLookup .collisionChain currentEntries.length
        (MapWork.keyWork arithmetic currentEntries key) + 3) value afterArguments := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.expr (.call (.attribute base "get") expressions) env, stack, heap⟩ 1
      ⟨.expr base env, .methodReceiver "get" expressions env :: stack, heap⟩ :=
    advance (by cases base <;> simp_all [step, Option.isSome_iff_ne_none])
      (by simp [charge, attributeCallEntry]) rfl
  have bound : Reaches arithmetic module anchors
      ⟨.value (.ref address), .methodReceiver "get" expressions env :: stack, afterReceiver⟩ 1
      (argumentsState (.dictionaryGet address) env [] expressions stack afterReceiver) :=
    advance (by simp [step, run, bindMethod, found])
      (by simp [charge, RecordWork.method, found]) (by cases expressions <;> rfl)
  have last : Reaches arithmetic module anchors
      ⟨.operation (.dictionaryGet address) values, stack, afterArguments⟩
      (mapLookup .collisionChain currentEntries.length
        (MapWork.keyWork arithmetic currentEntries key) + 1)
      ⟨.value value, stack, afterArguments⟩ := by
    apply advance
    · simp only [step, result, run, evaluated, protectGenerator_next]
    · rcases arity with rfl | ⟨fallback, rfl⟩ <;>
        simp [charge, operation, BufferWork.operation, MapWork.operation, MapWork.lookup, current]
    · rfl
  exact (((((first.trans (receiver anchors _)).trans bound).trans
    (arguments.reaches (completed := []) (.dictionaryGet address) anchors stack)).trans last)).mono (by omega)

end EvaluatesIn
end FormalSW.PyAst.HeapCalls.Runtime
