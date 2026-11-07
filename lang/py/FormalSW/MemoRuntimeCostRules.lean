import lang.py.FormalSW.MemoRuntimeCost

/-! Compositional runtime bounds for memoized source calls. The work budget bounds
both ordinary operation costs and cache growth. The resulting quadratic envelope
charges collision-chain lookup against the evolving table size. -/
namespace FormalSW.PyAst.MemoCalls.Runtime
open PrimitiveWork

/-- A uniform key-width bound justified by the semantic cache specification. -/
def KeyBound (arithmetic : Arithmetic) (spec : Specification) (width : Nat) : Prop :=
  ∀ key value, spec key value → key.structuredArguments = none ∧ keyWork arithmetic key ≤ width

def envelope (width size work : Nat) : Nat := work * (size + work + 1) * (4 * (width + 1))

theorem envelope_mono (small : a ≤ b) : envelope width size a ≤ envelope width size b := by
  unfold envelope
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul small (by omega))

theorem envelope_add (growth : middle ≤ size + a) :
    envelope width size a + envelope width middle b ≤ envelope width size (a + b) := by
  unfold envelope
  rw [← Nat.add_mul]
  apply Nat.mul_le_mul_right
  have left := Nat.mul_le_mul_left a (show size + a + 1 ≤ size + (a+b) + 1 by omega)
  have right := Nat.mul_le_mul_left b (show middle + b + 1 ≤ size + (a+b) + 1 by omega)
  simpa only [Nat.add_mul] using Nat.add_le_add left right

theorem work_le_envelope (width size work : Nat) : work ≤ envelope width size work := by
  unfold envelope
  exact Nat.le_trans (Nat.le_mul_of_pos_right work (by omega))
    (Nat.le_mul_of_pos_right _ (by omega))

/-- Every occupied cache slot has a key allowed by the semantic invariant. -/
theorem represented_key_bound (priced : KeyBound arithmetic spec width)
    (valid : cache.Valid spec) (represented : Represents keys cache) (present : key ∈ keys) :
    key.structuredArguments = none ∧ keyWork arithmetic key ≤ width := by
  have occupied := (represented.2 key).mpr present
  cases found : cache key with
  | none => exact False.elim (occupied found)
  | some value => exact priced key value (valid key value found)

theorem widestKey_le (bounded : ∀ key ∈ keys, keyWork arithmetic key ≤ width) :
    widestKey arithmetic keys ≤ width := by
  have fold : ∀ (items : List Key) (initial : Nat), initial ≤ width →
      (∀ key ∈ items, keyWork arithmetic key ≤ width) →
      (items.map (keyWork arithmetic)).foldl max initial ≤ width := by
    intro items
    induction items with
    | nil => intro initial small _; exact small
    | cons head tail ih =>
      intro initial small bounded
      exact ih (max initial (keyWork arithmetic head))
        (Nat.max_le.mpr ⟨small, bounded head (by simp)⟩)
        (fun key present => bounded key (by simp [present]))
  exact fold keys 0 (by omega) bounded

theorem lookupWork_bound (priced : KeyBound arithmetic spec width)
    (valid : cache.Valid spec) (represented : Represents keys cache)
    (allowed : key.structuredArguments = none) (widthBound : keyWork arithmetic key ≤ width) :
    ∃ amount, lookupWork arithmetic keys key = some amount ∧
      amount + keyWork arithmetic key + 1 ≤ envelope width keys.length 1 := by
  have bounded := fun query present => represented_key_bound priced valid represented (key := query) present
  have all : keys.all (fun entry => entry.structuredArguments.isNone) = true := by
    apply List.all_eq_true.mpr
    intro entry present
    simp [(bounded entry present).1]
  have widest := widestKey_le (fun entry present => (bounded entry present).2)
  refine ⟨mapLookup .collisionChain keys.length (keyWork arithmetic key + widestKey arithmetic keys), ?_, ?_⟩
  · simp [lookupWork, allowed, all]
  · have comparisonBound : keyWork arithmetic key + widestKey arithmetic keys + 1 ≤ 4 * (width + 1) := by omega
    have lookupBound := Nat.mul_le_mul_left (keys.length + 1) comparisonBound
    have total := Nat.add_le_add lookupBound (show keyWork arithmetic key + 1 ≤ 4 * (width + 1) by omega)
    simpa [envelope, mapLookup, Nat.add_mul, Nat.add_assoc, Nat.two_mul] using total

/-- Quantification over cache contents makes recursive calls compositional. -/
def RunsIn (arithmetic : Arithmetic) (module : Module) (memoized : List String)
    (spec : Specification) (width : Nat) (initial : Calls.State) (work : Nat) (final : Calls.State) : Prop :=
  ∀ callers cache keys, cache.Valid spec → Represents keys cache →
    ∃ updated updatedKeys cost,
      updated.Valid spec ∧ Represents updatedKeys updated ∧ updatedKeys.length ≤ keys.length + work ∧
      cost ≤ envelope width keys.length work ∧
      RuntimeCost.Reaches (step module memoized) (charge arithmetic module memoized)
        ⟨⟨initial, callers, cache⟩, keys⟩ cost ⟨⟨final, callers, updated⟩, updatedKeys⟩

namespace RunsIn

theorem refl : RunsIn arithmetic module memoized spec width state 0 state := by
  intro callers cache keys valid represented
  exact ⟨cache, keys, 0, valid, represented, by omega, by simp [envelope], .refl⟩

theorem mono (run : RunsIn arithmetic module memoized spec width initial a final) (larger : a ≤ b) :
    RunsIn arithmetic module memoized spec width initial b final := by
  intro callers cache keys valid represented
  obtain ⟨updated, updatedKeys, cost, valid, represented, growth, upper, run⟩ := run callers cache keys valid represented
  exact ⟨updated, updatedKeys, cost, valid, represented, by omega, Nat.le_trans upper (envelope_mono larger), run⟩

theorem trans (first : RunsIn arithmetic module memoized spec width initial a middle)
    (second : RunsIn arithmetic module memoized spec width middle b final) :
    RunsIn arithmetic module memoized spec width initial (a+b) final := by
  intro callers cache keys valid represented
  obtain ⟨mid, midKeys, ca, valid, represented, growth, upperA, runA⟩ := first callers cache keys valid represented
  obtain ⟨last, lastKeys, cb, valid, represented, growthB, upperB, runB⟩ := second callers mid midKeys valid represented
  exact ⟨last, lastKeys, ca+cb, valid, represented, by omega,
    Nat.le_trans (Nat.add_le_add upperA upperB) (envelope_add growth), runA.trans runB⟩

end RunsIn

private theorem transparent_written (plain : transparent memoized current) :
    written ⟨current, callers, cache⟩ = none := by
  rcases current with ⟨work, stack⟩
  cases work <;> try rfl
  case value value =>
    cases stack with
    | nil => exact False.elim plain
    | cons => rfl

private theorem transparent_charge (plain : transparent memoized current) :
    charge arithmetic module memoized ⟨⟨current, callers, cache⟩, keys⟩ =
      Calls.Runtime.charge arithmetic module current := by
  rcases current with ⟨work, stack⟩
  cases work <;> try rfl
  case value value =>
    cases stack with
    | nil => exact False.elim plain
    | cons => rfl
  case invoke name values =>
    simp only [transparent] at plain
    simp [charge, plain]

theorem RunsIn.raw (plain : transparent memoized initial)
    (transition : Calls.step module initial = .next following)
    (measured : Calls.Runtime.charge arithmetic module initial = some amount) :
    RunsIn arithmetic module memoized spec width initial amount following := by
  intro callers cache keys valid represented
  refine ⟨cache, keys, amount, valid, represented, by omega, work_le_envelope _ _ _, ?_⟩
  have moved := MemoCalls.step_raw (callers := callers) (cache := cache) plain transition
  have unchanged := transparent_written (callers := callers) (cache := cache) plain
  have priced := transparent_charge (arithmetic := arithmetic) (module := module)
    (callers := callers) (cache := cache) (keys := keys) plain
  simpa only [Nat.add_zero] using RuntimeCost.Reaches.next
    (step := step module memoized) (charge := charge arithmetic module memoized)
    (state := ⟨⟨initial, callers, cache⟩, keys⟩)
    (following := ⟨⟨following, callers, cache⟩, keys⟩)
    (by simp [step, moved, nextKeys, unchanged]) (priced.trans measured) .refl

end FormalSW.PyAst.MemoCalls.Runtime
