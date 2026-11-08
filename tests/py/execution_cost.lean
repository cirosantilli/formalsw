import lang.py.FormalSW.CallsCost
import lang.py.FormalSW.AllocationCost
import lang.py.FormalSW.BufferCost

/-! Cost-model regressions: unsupported and divergent executions cannot acquire
finite cost certificates; exact counts compose and agree with termination. -/
open FormalSW.PyAst

private abbrev countdown : Execution Nat :=
  ⟨Nat, 3, fun n => match n with | 0 => .done (.ok 7) | n + 1 => .next n⟩

example : FinishesIn countdown.step countdown.initial 4 (.ok 7) :=
  .next rfl (.next rfl (.next rfl (.done rfl)))

example : countdown.TimeBound 4 :=
  Execution.timeBound_of_observe (outcome := .ok 7) rfl

example : ¬ countdown.TimeBound 3 := by
  rintro ⟨cost, outcome, run, bounded⟩
  have exactRun : FinishesIn countdown.step countdown.initial 4 (.ok 7) :=
    .next rfl (.next rfl (.next rfl (.done rfl)))
  have := run.unique exactRun
  omega

example : ¬ (Execution.unsupported : Execution Nat).TimeBound bound := by
  rintro ⟨cost, outcome, run, _⟩
  cases run <;> contradiction

private def forever : Execution Nat := ⟨Unit, (), fun _ => .next ()⟩

example : ¬ forever.TimeBound bound := by
  intro bounded
  apply Execution.diverges_not_halts (execution := forever) ?_ bounded.halts
  exact ⟨fun _ => True, trivial, fun _ _ => ⟨(), rfl, trivial⟩⟩

example (execution : Execution Nat) : execution.Halts ↔ ∃ bound, execution.TimeBound bound := by
  constructor
  · rintro ⟨outcome, run⟩
    obtain ⟨cost, run⟩ := run.exists_cost
    exact ⟨cost, cost, outcome, run, Nat.le_refl _⟩
  · rintro ⟨bound, run⟩
    exact run.halts

/-- Multiple argument families quantify uniformly over all inputs of a size. -/
example : Execution.IsBigO (fun pair : Nat × Nat => Execution.pure (pair.1 + pair.2))
    (fun _ => True) (fun pair => pair.1 + pair.2) (fun _ => 1) := by
  exact ⟨1, 0, fun _ _ _ => ⟨1, _, .done rfl, by simp⟩⟩

/-- Weights count work on the same trace; four countdown transitions cost ten. -/
example : FinishesWith countdown.step (fun n => n + 1) countdown.initial 10 (.ok 7) := by
  have terminal : FinishesWith countdown.step (fun n => n + 1) 0 1 (.ok 7) :=
    FinishesWith.done (step := countdown.step) rfl
  have one := FinishesWith.next (step := countdown.step) (state := 1) rfl terminal
  have two := FinishesWith.next (step := countdown.step) (state := 2) rfl one
  exact FinishesWith.next (step := countdown.step) (state := 3) rfl two

example : ¬ forever.WeightedTimeBound (fun _ => 1) bound := by
  intro bounded
  apply Execution.diverges_not_halts (execution := forever) ?_ bounded.halts
  exact ⟨fun _ => True, trivial, fun _ _ => ⟨(), rfl, trivial⟩⟩

/-- An actual two-element list slice pays for two copied slots plus its transition. -/
example : HeapCalls.AllocationCost.charge { body := [] } 1
    ⟨.operation .slice [.ref 0, .scalar .none, .scalar (.int 2), .scalar .none], [],
      [.list [.scalar (.int 3), .scalar (.int 4), .scalar (.int 5)]]⟩ = 3 := by decide

/-- Three writes still cost three when every stored byte was already zero. -/
example : HeapCalls.BufferCost.charge { body := [] } 1
    ⟨.operation (.setSlice (.scalar (.bytes [0, 0, 0])))
      [.ref 0, .scalar (.int 1), .scalar .none, .scalar (.int 3)], [],
      [.bytearray (List.replicate 10 0)]⟩ = 4 := by decide

/-- Constructing the bytes used by a slice write pays for each output byte. -/
example : HeapCalls.BufferCost.charge { body := [] } 0
    ⟨.value (.scalar (.int 7)), [.binaryRight .mult (.scalar (.bytes [0])) false], []⟩ = 8 := by decide

/-- Bytearray multiplication allocates its output, even though it is one primitive. -/
example : HeapCalls.BufferCost.charge { body := [] } 1
    ⟨.value (.scalar (.int 7)), [.binaryRight .mult (.ref 0) false], [.bytearray [1]]⟩ = 8 := by decide

/-- Supported iterable replacements pay for every byte written too. -/
example : HeapCalls.BufferCost.charge { body := [] } 2
    ⟨.operation (.setSlice (.ref 1))
      [.ref 0, .scalar (.int 1), .scalar .none, .scalar (.int 3)], [],
      [.bytearray (List.replicate 10 0), .list (List.replicate 3 (.scalar (.int 0)))]⟩ = 4 := by decide

example : HeapCalls.BufferCost.charge { body := [] } 2
    ⟨.operation (.setSlice (.ref 1))
      [.ref 0, .scalar (.int 1), .scalar .none, .scalar (.int 3)], [],
      [.bytearray (List.replicate 10 0), .tuple (List.replicate 3 (.scalar (.int 0)))]⟩ = 4 := by decide
