import lang.py.FormalSW.DictionaryCalls
import lang.py.FormalSW.HeapRuntimeCostBuffers

/-! Scalar dictionary displays, subscripts and get calls pay for the current table size and
key widths. Constant displays retain Python's duplicate-key insertion semantics. -/
namespace FormalSW.PyAst.HeapCalls.Runtime
variable {globals : Mutable.Globals}
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

/-- Integer keys occupy one word each; a collision chain still pays for every
entry and for the unsuccessful-search slot. -/
theorem dictionary_lookup_word_int_le (entries : List (Constant × Value)) (key : Int)
    (integerKeys : ∀ entry ∈ entries, ∃ value : Int, entry.1 = .int value) :
    mapLookup .collisionChain entries.length (MapWork.keyWork .word entries (.int key)) ≤
      3 * (entries.length + 1) := by
  have foldBound (items : List Nat) (initial : Nat)
      (bounded : ∀ item ∈ items, item ≤ 1) (initialBound : initial ≤ 1) :
      items.foldl max initial ≤ 1 := by
    induction items generalizing initial with
    | nil => exact initialBound
    | cons head tail ih =>
        have headBound := bounded head (by simp)
        have tailBound : ∀ item ∈ tail, item ≤ 1 := by
          intro item member
          exact bounded item (by simp [member])
        exact ih (max initial head) tailBound (by omega)
  have widths : ∀ width ∈ entries.map (fun entry => scalarSize .word entry.1), width ≤ 1 := by
    intro width member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨value, equal⟩ := integerKeys entry entryMember
    simp [equal, scalarSize, integer]
  have widest := foldBound (entries.map fun entry => scalarSize .word entry.1) 0 widths (by omega)
  have keyBound : MapWork.keyWork .word entries (.int key) ≤ 2 := by
    change 1 + (entries.map fun entry => scalarSize .word entry.1).foldl max 0 ≤ 2
    omega
  calc
    mapLookup .collisionChain entries.length (MapWork.keyWork .word entries (.int key))
        ≤ (entries.length + 1) * 3 :=
      Nat.mul_le_mul_left _ (by omega : MapWork.keyWork .word entries (.int key) + 1 ≤ 3)
    _ = 3 * (entries.length + 1) := Nat.mul_comm _ _

theorem dictionary_lookup_word_int_le_33 (entries : List (Constant × Value)) (key : Int)
    (count : entries.length ≤ 10)
    (integerKeys : ∀ entry ∈ entries, ∃ value : Int, entry.1 = .int value) :
    mapLookup .collisionChain entries.length (MapWork.keyWork .word entries (.int key)) ≤ 33 := by
  have bounded := dictionary_lookup_word_int_le entries key integerKeys
  omega

theorem dictionary_constants_reach (pairs : List (Constant × Constant))
    (entries : List (Constant × Value)) :
    Reaches (globals := globals) arithmetic module anchors
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
      have first : Reaches (globals := globals) arithmetic module anchors
          ⟨.dictionary ((.constant key, .constant value) ::
            rest.map (fun (key, value) => (.constant key, .constant value))) entries env, stack, heap⟩ 1
          ⟨.expr (.constant key) env, .dictionaryKey (.constant value)
            (rest.map fun (key, value) => (.constant key, .constant value)) entries env :: stack, heap⟩ :=
        advance rfl rfl rfl
      have next : Reaches (globals := globals) arithmetic module anchors
          ⟨.value (.scalar key), .dictionaryKey (.constant value)
            (rest.map fun (key, value) => (.constant key, .constant value)) entries env :: stack, heap⟩ 1
          ⟨.expr (.constant value) env, .dictionaryValue key
            (rest.map fun (key, value) => (.constant key, .constant value)) entries env :: stack, heap⟩ :=
        advance rfl rfl rfl
      have inserted : Reaches (globals := globals) arithmetic module anchors
          ⟨.value (.scalar value), .dictionaryValue key
            (rest.map fun (key, value) => (.constant key, .constant value)) entries env :: stack, heap⟩
          (mapLookup .collisionChain entries.length (MapWork.keyWork arithmetic entries key) + 2)
          ⟨.dictionary (rest.map fun (key, value) => (.constant key, .constant value))
            (ScalarDict.insert entries key (.scalar value)) env, stack, heap⟩ := advance rfl rfl rfl
      exact (((((first.trans (EvaluatesIn.constant (globals := globals) anchors _)).trans next).trans
        (EvaluatesIn.constant (globals := globals) anchors _)).trans inserted).trans (ih _)).mono
          (by simp only [dictionaryEntriesBudget]; omega)

namespace EvaluatesIn

/-- Read the live dictionary after evaluating the index, which may mutate it.
The budget includes entry, both argument frames and the lookup transition. -/
theorem dictionary_subscript (ordinary : ∀ a b c, index ≠ .slice a b c)
    (receiver : EvaluatesIn (globals := globals) arithmetic module env base heap ca (.ref address) middle)
    (position : EvaluatesIn (globals := globals) arithmetic module env index middle cb (.scalar key) afterIndex)
    (found : afterIndex[address]? = some (.dict entries))
    (present : ScalarDict.lookup entries key = some value) :
    EvaluatesIn (globals := globals) arithmetic module env (.subscript base index) heap
      (ca + cb + mapLookup .collisionChain entries.length
        (MapWork.keyWork arithmetic entries key) + 5) value afterIndex := by
  intro anchors stack
  have initial : Reaches (globals := globals) arithmetic module anchors
      ⟨.expr (.subscript base index) env, stack, heap⟩ 1
      (argumentsState .subscript env [] [base, index] stack heap) :=
    advance (by cases index <;> simp_all [step, argumentsState]) rfl rfl
  have args := (ArgumentsIn.cons receiver (ArgumentsIn.cons position ArgumentsIn.nil)).reaches
    (completed := []) .subscript anchors stack
  have evaluated := Mutable.getItem_dictionary afterIndex address entries found key present
  have last : Reaches (globals := globals) arithmetic module anchors
      ⟨.operation .subscript [.ref address, .scalar key], stack, afterIndex⟩
      (mapLookup .collisionChain entries.length (MapWork.keyWork arithmetic entries key) + 1)
      ⟨.value value, stack, afterIndex⟩ :=
    advance (by simp [step, primitive, result, run, evaluated])
      (by cases key <;>
        simp [charge, operation, BufferWork.operation, scalarNumber, MapWork.operation, MapWork.lookup, found]) rfl
  exact ((initial.trans args).trans last).mono (by simp; omega)

theorem dictionary_constants (pairs : List (Constant × Constant)) :
    EvaluatesIn (globals := globals) arithmetic module env
      (.dict (pairs.map fun (key, value) => (.constant key, .constant value)))
      heap (dictionaryLiteralBudget pairs arithmetic) (.ref heap.length)
      (heap ++ [.dict (dictionaryContents pairs)]) := by
  intro anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.expr (.dict (pairs.map fun (key, value) => (.constant key, .constant value))) env, stack, heap⟩ 1
      ⟨.dictionary (pairs.map fun (key, value) => (.constant key, .constant value)) [] env, stack, heap⟩ :=
    advance rfl rfl rfl
  exact first.trans (dictionary_constants_reach (globals := globals) pairs [])

/-- Bind before evaluating arguments, then price the live dictionary. The result
proof may choose a present value or the supplied (or implicit None) default. -/
theorem dictionary_get
    (localName : ∀ name, base = .name name → env name ≠ none)
    (receiver : EvaluatesIn (globals := globals) arithmetic module env base heap cr (.ref address) afterReceiver)
    (found : afterReceiver[address]? = some (.dict entries))
    (arguments : ArgumentsIn (globals := globals) arithmetic module env 0 expressions afterReceiver ca values afterArguments)
    (current : afterArguments[address]? = some (.dict currentEntries))
    (arity : values = [.scalar key] ∨ ∃ fallback, values = [.scalar key, fallback])
    (evaluated : primitive (.dictionaryGet address) values afterArguments =
      some (.ok value, afterArguments)) :
    EvaluatesIn (globals := globals) arithmetic module env (.call (.attribute base "get") expressions) heap
      (cr + ca + mapLookup .collisionChain currentEntries.length
        (MapWork.keyWork arithmetic currentEntries key) + 3) value afterArguments := by
  intro anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.expr (.call (.attribute base "get") expressions) env, stack, heap⟩ 1
      ⟨.expr base env, .methodReceiver "get" expressions env :: stack, heap⟩ :=
    advance (by cases base <;> simp_all [step, Option.isSome_iff_ne_none])
      (by simp [charge, attributeCallEntry]) rfl
  have bound : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.ref address), .methodReceiver "get" expressions env :: stack, afterReceiver⟩ 1
      (argumentsState (.dictionaryGet address) env [] expressions stack afterReceiver) :=
    advance (by simp [step, run, bindMethod, found])
      (by simp [charge, RecordWork.method, found]) (by cases expressions <;> rfl)
  have last : Reaches (globals := globals) arithmetic module anchors
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
