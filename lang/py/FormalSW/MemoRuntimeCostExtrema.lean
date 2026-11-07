import lang.py.FormalSW.MemoRuntimeCostFunctions

namespace FormalSW.PyAst.MemoCalls.Runtime
open PrimitiveWork

def ExtremumReturnsIn (arithmetic : Arithmetic) (module : Module) (memoized : List String)
    (spec : Specification) (width : Nat) (range : Calls.RangeExtremum) (current : Int)
    (best : Option (Int × Constant)) (work : Nat) (result : Int) : Prop :=
  ∀ stack, RunsIn arithmetic module memoized spec width
    ⟨.extremumLoop range current best, stack⟩ work ⟨.value (.int result), stack⟩

theorem ExtremumReturnsIn.mono
    (run : ExtremumReturnsIn arithmetic module memoized spec width range current best a value)
    (larger : a ≤ b) : ExtremumReturnsIn arithmetic module memoized spec width range current best b value :=
  fun stack => (run stack).mono larger

theorem ExtremumReturnsIn.done (finished : Calls.rangeContinues current range.stop range.stride = false) :
    ExtremumReturnsIn arithmetic module memoized spec width range current (some (winner, score))
      (Calls.Runtime.rangeWork arithmetic current range.stop range.stride) winner := by
  intro stack
  exact RunsIn.raw (by trivial) (by simp [Calls.step, finished]) rfl

theorem ExtremumReturnsIn.next (continues : Calls.rangeContinues current range.stop range.stride = true)
    (key : ReturnsIn arithmetic module memoized spec width range.key [.int current] ck score)
    (selected : range.choose current score best = .ok updated)
    (measured : ∀ stack, Calls.Runtime.charge arithmetic module
      ⟨.value score, .extremumKey range current best :: stack⟩ = some cs)
    (rest : ExtremumReturnsIn arithmetic module memoized spec width range
      (current + range.stride) (some updated) cr result) :
    ExtremumReturnsIn arithmetic module memoized spec width range current best
      (Calls.Runtime.rangeWork arithmetic current range.stop range.stride + ck + cs + cr) result := by
  intro stack
  have first : RunsIn arithmetic module memoized spec width
      ⟨.extremumLoop range current best, stack⟩
      (Calls.Runtime.rangeWork arithmetic current range.stop range.stride)
      ⟨.invoke range.key [.int current], .extremumKey range current best :: stack⟩ :=
    RunsIn.raw (by trivial) (by simp [Calls.step, continues]) rfl
  have choose : RunsIn arithmetic module memoized spec width
      ⟨.value score, .extremumKey range current best :: stack⟩ cs
      ⟨.extremumLoop range (current + range.stride) (some updated), stack⟩ :=
    RunsIn.raw (by trivial) (by simp [Calls.step, selected]) (measured stack)
  exact ((first.trans (key _)).trans choose).trans (rest stack)

theorem EvaluatesIn.extremum_single_range
    (argument : EvaluatesIn arithmetic module memoized spec width env expression ca argumentValue)
    (bounds : Calls.rangeBounds [argumentValue] = .ok (start, stop, stride))
    (priced : ∀ stack, Calls.Runtime.charge arithmetic module
      ⟨.startExtremum maximum key [argumentValue], stack⟩ = some setup)
    (rest : ExtremumReturnsIn arithmetic module memoized spec width
      ⟨maximum, key, stop, stride⟩ start none cr result) :
    EvaluatesIn arithmetic module memoized spec width env (.extremumRange maximum [expression] key)
      (ca + setup + cr + 2) (.int result) := by
  intro stack
  have first : RunsIn arithmetic module memoized spec width
      ⟨.expr (.extremumRange maximum [expression] key) env, stack⟩ 1
      ⟨.expr expression env, .extremumArguments maximum key [] [] env :: stack⟩ :=
    RunsIn.raw (by trivial) rfl rfl
  have ready : RunsIn arithmetic module memoized spec width
      ⟨.value argumentValue, .extremumArguments maximum key [] [] env :: stack⟩ 1
      ⟨.startExtremum maximum key [argumentValue], stack⟩ := RunsIn.raw (by trivial) rfl rfl
  have started : RunsIn arithmetic module memoized spec width
      ⟨.startExtremum maximum key [argumentValue], stack⟩ setup
      ⟨.extremumLoop ⟨maximum, key, stop, stride⟩ start none, stack⟩ :=
    RunsIn.raw (by trivial) (by simp [Calls.step, bounds]) (priced stack)
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (((first.trans (argument _)).trans ready).trans started).trans (rest stack)

end FormalSW.PyAst.MemoCalls.Runtime
