import lang.py.FormalSW.MemoRuntimeCostRules

namespace FormalSW.PyAst.MemoCalls.Runtime
open PrimitiveWork

def EvaluatesIn (arithmetic : Arithmetic) (module : Module) (memoized : List String)
    (spec : Specification) (width : Nat) (env : ScalarEnv) (expression : Expr)
    (work : Nat) (value : Constant) : Prop :=
  ∀ stack, RunsIn arithmetic module memoized spec width
    ⟨.expr expression env, stack⟩ work ⟨.value value, stack⟩

def BlockReturnsIn (arithmetic : Arithmetic) (module : Module) (memoized : List String)
    (spec : Specification) (width : Nat) (env : ScalarEnv) (body : List Stmt)
    (work : Nat) (value : Constant) : Prop :=
  ∀ stack, RunsIn arithmetic module memoized spec width
    ⟨.block body env, stack⟩ work ⟨.value value, stack⟩

def ReturnsIn (arithmetic : Arithmetic) (module : Module) (memoized : List String)
    (spec : Specification) (width : Nat) (name : String) (values : List Constant)
    (work : Nat) (value : Constant) : Prop :=
  ∀ stack, RunsIn arithmetic module memoized spec width
    ⟨.invoke name values, stack⟩ work ⟨.value value, stack⟩

theorem ReturnsIn.mono (run : ReturnsIn arithmetic module memoized spec width name values a value)
    (larger : a ≤ b) : ReturnsIn arithmetic module memoized spec width name values b value :=
  fun stack => (run stack).mono larger

theorem ReturnsIn.timeBound
    (run : ReturnsIn arithmetic module memoized spec width name values work value) :
    TimeBound arithmetic module memoized name values (envelope width 0 work + 1) := by
  obtain ⟨updated, keys, cost, _, _, _, bounded, reached⟩ :=
    run [] [] Cache.empty [] (Cache.valid_empty spec) represents_empty
  exact ⟨cost+1, .ok value, reached.finishes (.done rfl rfl), by simpa using Nat.add_le_add_right bounded 1⟩

theorem BlockReturnsIn.function (plain : name ∉ memoized)
    (found : findFunctionIn module.body name = some (args, body))
    (arity : args.length = values.length)
    (run : BlockReturnsIn arithmetic module memoized spec width
      (argumentEnv args values) (executableBody body) work value) :
    ReturnsIn arithmetic module memoized spec width name values (values.length+1+work) value := by
  intro stack
  exact (RunsIn.raw (initial := ⟨.invoke name values, stack⟩) plain (by simp [Calls.step, found, arity])
    (by simp [Calls.Runtime.charge, found])).trans (run stack)

/-- Hits pay key construction and lookup. Misses additionally execute the source
body and write its proven result back to the actual memoization cache. -/
theorem BlockReturnsIn.memoized_function (priced : KeyBound arithmetic spec width)
    (cached : name ∈ memoized)
    (found : findFunctionIn module.body name = some (args, body))
    (arity : args.length = values.length)
    (run : BlockReturnsIn arithmetic module memoized spec width
      (argumentEnv args (values.map Constant.int)) (executableBody body) work value)
    (correct : spec ⟨name, values, none⟩ value)
    (unique : ∀ other, spec ⟨name, values, none⟩ other → other = value) :
    ReturnsIn arithmetic module memoized spec width name (values.map Constant.int)
      (values.length + 2 + work + 1) value := by
  intro stack callers cache keys valid represented
  let key : Key := ⟨name, values, none⟩
  have keyBound := priced key value correct
  obtain ⟨lookup, measured, upper⟩ := lookupWork_bound priced valid represented keyBound.1 keyBound.2
  dsimp only [key] at measured
  cases hit : cache key with
  | some other =>
    dsimp only [key] at hit
    have equal := unique other (valid key other hit)
    subst other
    refine ⟨cache, keys, lookup + keyWork arithmetic key + 1, valid, represented, by omega,
      Nat.le_trans upper (envelope_mono (by omega)), ?_⟩
    simpa only [Nat.add_zero] using RuntimeCost.Reaches.next
      (step := step module memoized) (charge := charge arithmetic module memoized)
      (state := ⟨⟨⟨.invoke name (values.map Constant.int), stack⟩, callers, cache⟩, keys⟩)
      (following := ⟨⟨⟨.value value, stack⟩, callers, cache⟩, keys⟩)
      (by simp [step, MemoCalls.step, cached, hit, nextKeys, written])
      (by simp [charge, cached, key, hit, measured]) .refl
  | none =>
    dsimp only [key] at hit
    obtain ⟨updated, updatedKeys, bodyCost, preserved, representedAfter, growth, bodyUpper, bodyRun⟩ :=
      run [] (⟨key, stack⟩ :: callers) cache keys valid represented
    obtain ⟨writeLookup, writeMeasured, writeUpper⟩ :=
      lookupWork_bound priced preserved representedAfter keyBound.1 keyBound.2
    dsimp only [key] at writeMeasured
    have entryUpper : lookup + keyWork arithmetic key + (values.length+1) ≤
        envelope width keys.length (values.length+2) := by
      have sum := Nat.add_le_add upper (work_le_envelope width keys.length (values.length+1))
      have combined := envelope_add (width := width) (size := keys.length)
        (middle := keys.length) (a := 1) (b := values.length+1) (by omega)
      have total := Nat.le_trans sum combined
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.le_trans (by omega : lookup + keyWork arithmetic key + (values.length+1) ≤
          (lookup + keyWork arithmetic key + 1) + (values.length+1)) total
    have beforeWrite := Nat.le_trans (Nat.add_le_add entryUpper bodyUpper)
      (envelope_add (middle := keys.length) (by omega))
    have costUpper := Nat.le_trans
      (Nat.add_le_add beforeWrite (Nat.le_trans (by omega : writeLookup+1 ≤
        writeLookup + keyWork arithmetic key + 1) writeUpper))
      (envelope_add (by omega : updatedKeys.length ≤ keys.length + (values.length+2+work)))
    refine ⟨updated.insert key value, recordKey updatedKeys key,
      (lookup + keyWork arithmetic key + (values.length+1)) + bodyCost + (writeLookup+1),
      preserved.insert correct, representedAfter.insert key value, ?_, costUpper, ?_⟩
    · have recorded := recordKey_length updatedKeys key
      omega
    · have entry : RuntimeCost.Reaches (step module memoized) (charge arithmetic module memoized)
          ⟨⟨⟨.invoke name (values.map Constant.int), stack⟩, callers, cache⟩, keys⟩
          (lookup + keyWork arithmetic key + (values.length+1))
          ⟨⟨⟨.block (executableBody body) (argumentEnv args (values.map Constant.int)), []⟩,
            ⟨key, stack⟩ :: callers, cache⟩, keys⟩ := by
        simpa only [Nat.add_zero] using RuntimeCost.Reaches.next
          (by simp [step, MemoCalls.step, cached, key, hit, Calls.step, found, arity, nextKeys, written])
          (by simp [charge, cached, key, hit, measured, Calls.Runtime.charge, found]) .refl
      have write : RuntimeCost.Reaches (step module memoized) (charge arithmetic module memoized)
          ⟨⟨⟨.value value, []⟩, ⟨key, stack⟩ :: callers, updated⟩, updatedKeys⟩ (writeLookup+1)
          ⟨⟨⟨.value value, stack⟩, callers, updated.insert key value⟩, recordKey updatedKeys key⟩ := by
        apply RuntimeCost.Reaches.next (cost := 0) (amount := writeLookup+1)
        · rfl
        · simp [charge, key, writeMeasured]
        · exact .refl
      exact (entry.trans bodyRun).trans write

end FormalSW.PyAst.MemoCalls.Runtime
