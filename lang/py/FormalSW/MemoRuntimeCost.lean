import lang.py.FormalSW.MemoCalls
import lang.py.FormalSW.CallsRuntimeCost

/-! Runtime costs for the existing memoized interpreter. A list of distinct cache
keys records table size and key widths; execution still takes exactly one
`MemoCalls.step` per transition. Function identities have constant comparison
cost, while argument hashing/comparison and collision chains are size-sensitive. -/
namespace FormalSW.PyAst.MemoCalls.Runtime
open PrimitiveWork

-- Use decidable equality for metadata membership; the independently derived
-- Boolean equality on cache keys has no LawfulBEq instance.
local instance : BEq Key := ⟨fun left right => decide (left = right)⟩

/-- Add one cache key without counting a replacement as a new entry. -/
def recordKey (keys : List Key) (key : Key) : List Key :=
  if key ∈ keys then keys else key :: keys

@[simp] theorem mem_recordKey (query key : Key) (keys : List Key) :
    query ∈ recordKey keys key ↔ query = key ∨ query ∈ keys := by
  by_cases present : key ∈ keys <;> by_cases same : query = key <;>
    simp_all [recordKey]

theorem recordKey_length (keys : List Key) (key : Key) :
    (recordKey keys key).length ≤ keys.length + 1 := by
  unfold recordKey
  split <;> simp_all

/-- The metadata lists exactly the occupied cache slots. -/
def Represents (keys : List Key) (cache : Cache) : Prop :=
  keys.Nodup ∧ ∀ key, cache key ≠ none ↔ key ∈ keys

theorem represents_empty : Represents [] Cache.empty := by
  simp [Represents, Cache.empty]

theorem Represents.insert (represented : Represents keys cache) (key : Key) (value : Constant) :
    Represents (recordKey keys key) (cache.insert key value) := by
  constructor
  · unfold recordKey
    split
    · exact represented.1
    · exact List.nodup_cons.mpr ⟨by assumption, represented.1⟩
  · intro query
    by_cases same : query = key
    · subst query
      simp [Cache.insert]
    · simpa [Cache.insert, same] using represented.2 query

structure State where
  core : MemoCalls.State
  keys : List Key

/-- Only a successful memoized return writes the cache. -/
def written (state : MemoCalls.State) : Option (Key × Constant) :=
  match state.current, state.callers with
  | ⟨.value value, []⟩, caller :: _ => some (caller.key, value)
  | _, _ => none

/-- A transition changes the cache only when returning from a memoized call. -/
private theorem protect_next (state : MemoCalls.State) (result : Step MemoCalls.State Constant)
    (equal : protectGenerator state result = .next following) : result = .next following := by
  cases result with
  | next => exact equal
  | unsupported => cases equal
  | done result => cases result <;> cases equal

theorem cache_effect (transition : MemoCalls.step module memoized initial = .next following) :
    following.cache = match written initial with
      | some (key, value) => initial.cache.insert key value
      | none => initial.cache := by
  unfold MemoCalls.step at transition
  have raw := protect_next _ _ transition
  clear transition
  rcases initial with ⟨⟨work, stack⟩, callers, cache⟩
  cases work
  all_goals try {
    change (match Calls.step module _ with
      | .next current => (Step.next ⟨current, callers, cache⟩ : Step MemoCalls.State Constant)
      | .done result => .done result
      | .unsupported => .unsupported) = .next following at raw
    split at raw <;> cases raw
    rfl }
  case value value =>
    cases stack with
    | nil =>
      cases callers with
      | nil => cases raw
      | cons caller callers => cases raw; rfl
    | cons frame stack =>
      change (match Calls.step module _ with
        | .next current => (Step.next ⟨current, callers, cache⟩ : Step MemoCalls.State Constant)
        | .done result => .done result
        | .unsupported => .unsupported) = .next following at raw
      split at raw <;> cases raw
      rfl
  case invoke name values =>
    by_cases cached : name ∈ memoized
    · simp only [cached, ↓reduceIte] at raw
      split at raw
      · cases raw
      · split at raw
        · cases raw
          rfl
        · split at raw <;> cases raw
          rfl
    · simp only [cached, ↓reduceIte] at raw
      change (match Calls.step module _ with
        | .next current => (Step.next ⟨current, callers, cache⟩ : Step MemoCalls.State Constant)
        | .done result => .done result
        | .unsupported => .unsupported) = .next following at raw
      split at raw <;> cases raw
      rfl

def nextKeys (state : State) : List Key :=
  match written state.core with
  | some (key, _) => recordKey state.keys key
  | none => state.keys

def step (module : Module) (memoized : List String) (state : State) : Step State Constant :=
  match MemoCalls.step module memoized state.core with
  | .next core => .next ⟨core, nextKeys state⟩
  | .done outcome => .done outcome
  | .unsupported => .unsupported

theorem next_core (transition : step module memoized initial = .next following) :
    MemoCalls.step module memoized initial.core = .next following.core := by
  unfold step at transition
  split at transition <;> simp_all
  cases transition
  rfl

theorem next_keys (transition : step module memoized initial = .next following) :
    following.keys = nextKeys initial := by
  unfold step at transition
  split at transition <;> simp_all
  cases transition
  rfl

theorem done_core (transition : step module memoized state = .done outcome) :
    MemoCalls.step module memoized state.core = .done outcome := by
  unfold step at transition
  split at transition <;> simp_all

/-- The key list remains an exact representation, including replacement writes. -/
theorem represents_next (represented : Represents initial.keys initial.core.cache)
    (transition : step module memoized initial = .next following) :
    Represents following.keys following.core.cache := by
  rw [next_keys transition, cache_effect (next_core transition)]
  unfold nextKeys
  cases written initial.core with
  | none => exact represented
  | some pair => exact represented.insert pair.1 pair.2

theorem represents_reaches
    (run : RuntimeCost.Reaches (step module memoized) tariff initial cost final)
    (represented : Represents initial.keys initial.core.cache) :
    Represents final.keys final.core.cache := by
  induction run with
  | refl => exact represented
  | next transition _ _ ih => exact ih (represents_next represented transition)

/-- Metadata never changes the outcome or removes an interpreter transition. -/
theorem finishes_iff (state : State) :
    PyAst.Finishes (step module memoized) state outcome ↔
      PyAst.Finishes (MemoCalls.step module memoized) state.core outcome := by
  constructor
  · intro run
    induction run with
    | done transition => exact .done (done_core transition)
    | next transition _ ih => exact .next (next_core transition) ih
  · intro run
    generalize coreEq : state.core = core at run
    induction run generalizing state with
    | done transition => exact .done (by simp [step, coreEq, transition])
    | @next core following outcome transition _ ih =>
        exact .next (following := ⟨following, nextKeys state⟩)
          (by simp [step, coreEq, transition]) (ih _ rfl)

def function (module : Module) (memoized : List String) (name : String)
    (values : List Constant) : Execution Constant :=
  ⟨State, ⟨⟨⟨.invoke name values, []⟩, [], Cache.empty⟩, []⟩, step module memoized⟩

theorem function_equiv (module : Module) (memoized : List String) (name : String)
    (values : List Constant) :
    (function module memoized name values).Equiv (MemoCalls.function module memoized name values) := by
  intro outcome
  exact finishes_iff _

/-- The current scalar memo interpreter creates integer-argument keys. Other key
representations need their own cost rules and cannot receive an implicit unit tariff. -/
def keyWork (arithmetic : Arithmetic) (key : Key) : Nat :=
  1 + (key.arguments.map (integer arithmetic)).sum

def widestKey (arithmetic : Arithmetic) (keys : List Key) : Nat :=
  (keys.map (keyWork arithmetic)).foldl max 0

def lookupWork (arithmetic : Arithmetic) (keys : List Key) (key : Key)
    (maps : MapRepresentation := .collisionChain) : Option Nat :=
  if key.structuredArguments.isNone && keys.all (fun entry => entry.structuredArguments.isNone) then
    some (mapLookup maps keys.length (keyWork arithmetic key + widestKey arithmetic keys))
  else none

/-- A hit prices key construction and lookup; a miss also prices function entry.
A successful cached return pays for lookup and a value-reference write. -/
def charge (arithmetic : Arithmetic) (module : Module) (memoized : List String)
    (state : State) (maps : MapRepresentation := .collisionChain) : Option Nat :=
  match state.core.current, state.core.callers with
  | ⟨.value _, []⟩, caller :: _ => do
      let lookup ← lookupWork arithmetic state.keys caller.key maps
      return lookup + 1
  | ⟨.invoke name values, _⟩, _ =>
      if name ∈ memoized then do
        let arguments ← integerArguments values
        let key : Key := ⟨name, arguments, none⟩
        let lookup ← lookupWork arithmetic state.keys key maps
        let construction := keyWork arithmetic key
        match state.core.cache key with
        | some _ => return lookup + construction + 1
        | none => return lookup + construction + (← Calls.Runtime.charge arithmetic module state.core.current)
      else Calls.Runtime.charge arithmetic module state.core.current
  | _, _ => Calls.Runtime.charge arithmetic module state.core.current

def TimeBound (arithmetic : Arithmetic) (module : Module) (memoized : List String)
    (name : String) (values : List Constant) (bound : Nat)
    (maps : MapRepresentation := .collisionChain) : Prop :=
  RuntimeCost.TimeBound (function module memoized name values)
    (charge arithmetic module memoized · maps) bound

def IsBigO (arithmetic : Arithmetic) (module : Module) (memoized : List String)
    (name : String) (inputs : ι → List Constant) (domain : ι → Prop)
    (size : ι → Nat) (bound : Nat → Nat) (maps : MapRepresentation := .collisionChain) : Prop :=
  RuntimeCost.IsBigO (fun input => function module memoized name (inputs input))
    (fun _ state => charge arithmetic module memoized state maps) domain size bound

theorem TimeBound.halts_source (bounded : TimeBound arithmetic module memoized name values bound maps) :
    (MemoCalls.function module memoized name values).Halts := by
  obtain ⟨cost, outcome, run, _⟩ := bounded
  exact ⟨outcome, (finishes_iff _).mp run.execution⟩

end FormalSW.PyAst.MemoCalls.Runtime
