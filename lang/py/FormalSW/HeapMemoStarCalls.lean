import lang.py.FormalSW.HeapMemoCallRules

/-! Relational positional expansion retains arbitrary cached tuple addresses and live heap/cache effects. -/
namespace FormalSW.PyAst.HeapMemoCalls
variable {globals : Mutable.Globals}

@[simp] theorem expandedArgumentsState_heap (operation : HeapCalls.Operation) (env : Env) (done : List Value)
    (expressions : List Expr) (stack : List HeapCalls.Frame) (heap : Heap) :
    (HeapCalls.expandedArgumentsState operation env done expressions stack heap).heap = heap := by
  cases expressions with
  | nil => rfl
  | cons first rest =>
      cases found : HeapCalls.starSource? first <;> simp [HeapCalls.expandedArgumentsState, found]

/-- Expanded arguments may depend on cached references and on heaps reached by earlier expressions. -/
def StarArgumentsRel (module : Module) (spec : Specification) (env : Env) (expressions : List Expr)
    (heap : Heap) (post : List Value → Heap → Prop) (globals : Mutable.Globals := []) : Prop :=
  ∀ operation done anchors stack, RunsRel (globals := globals) module spec anchors
    (HeapCalls.expandedArgumentsState operation env done expressions stack heap)
    (fun final => ∃ values after,
      final = ⟨.operation operation (done ++ values), stack, after⟩ ∧ post values after)

namespace StarArgumentsRel

theorem nil (holds : post [] heap) : StarArgumentsRel (globals := globals) module spec env [] heap post := by
  intro operation done anchors stack
  exact RunsRel.refl ⟨[], heap, by simp [HeapCalls.expandedArgumentsState], holds⟩

theorem cons (ordinary : HeapCalls.starSource? expression = none)
    (head : EvaluatesRel (globals := globals) module spec env expression heap headPost)
    (tail : ∀ value middle, headPost value middle →
      StarArgumentsRel (globals := globals) module spec env expressions middle (fun values after => post (value :: values) after)) :
    StarArgumentsRel (globals := globals) module spec env (expression :: expressions) heap post := by
  intro operation done anchors stack
  simp only [HeapCalls.expandedArgumentsState, ordinary]
  apply (head anchors (.starredArguments operation done expressions env false :: stack)).bind
  rintro state ⟨value, middle, rfl, holds⟩
  apply RunsRel.next
    (current := ⟨.value value, .starredArguments operation done expressions env false :: stack, middle⟩)
    (following := HeapCalls.expandedArgumentsState operation env (done ++ [value]) expressions stack middle)
    (by trivial) (by simp [HeapCalls.step])
  apply (tail value middle holds operation (done ++ [value]) anchors stack).consequence
  rintro final ⟨values, after, rfl, holds⟩
  exact ⟨value :: values, after, by simp [List.append_assoc], holds⟩

theorem star (head : EvaluatesRel (globals := globals) module spec env expression heap headPost)
    (selected : ∀ value middle, headPost value middle →
      ∃ expanded afterExpansion,
        HeapCalls.starItems value middle = some (.ok expanded, afterExpansion) ∧
        Cache.Preserves spec middle afterExpansion ∧
        StarArgumentsRel (globals := globals) module spec env expressions afterExpansion
          (fun values after => post (expanded ++ values) after)) :
    StarArgumentsRel (globals := globals) module spec env (HeapCalls.starArgument expression :: expressions) heap post := by
  intro operation done anchors stack
  simp only [HeapCalls.expandedArgumentsState, HeapCalls.starArgument, HeapCalls.starSource?]
  apply (head anchors (.starredArguments operation done expressions env true :: stack)).bind
  rintro state ⟨value, middle, rfl, holds⟩
  obtain ⟨expanded, afterExpansion, expandedRun, preserved, tail⟩ := selected value middle holds
  apply RunsRel.next
    (current := ⟨.value value, .starredArguments operation done expressions env true :: stack, middle⟩)
    (following := HeapCalls.expandedArgumentsState operation env (done ++ expanded) expressions stack afterExpansion)
    (by trivial) (by simp [HeapCalls.step, HeapCalls.run, expandedRun]) ?_
    (by simpa only [expandedArgumentsState_heap] using preserved)
  apply (tail operation (done ++ expanded) anchors stack).consequence
  rintro final ⟨values, after, rfl, holds⟩
  exact ⟨expanded ++ values, after, by simp [List.append_assoc], holds⟩

end StarArgumentsRel

/-- Cache-aware calls receive the actual expanded vector only after all source arguments finish. -/
theorem EvaluatesRel.call_star
    (arguments : StarArgumentsRel (globals := globals) module spec env expressions heap argumentPost)
    (callee : ∀ values middle, argumentPost values middle → ReturnsRel (globals := globals) module spec name values middle post) :
    EvaluatesRel (globals := globals) module spec env (HeapCalls.starCall name expressions) heap post := by
  intro anchors stack
  apply RunsRel.next (current := ⟨.expr (HeapCalls.starCall name expressions) env, stack, heap⟩)
    (following := HeapCalls.expandedArgumentsState (.call name) env [] expressions stack heap)
    (by exact rfl) (by simp [HeapCalls.starCall, HeapCalls.step])
  apply (arguments (.call name) [] anchors stack).bind
  rintro final ⟨values, middle, rfl, holds⟩
  exact callee values middle holds anchors stack

end FormalSW.PyAst.HeapMemoCalls
