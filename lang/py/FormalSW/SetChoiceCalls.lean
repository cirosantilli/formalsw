import lang.py.FormalSW.SetCalls

/-! Source-loop entry and an arbitrary permitted choice from a live set. -/
namespace FormalSW.PyAst.SetCalls
open HeapCalls
set_option Elab.async false

theorem for_set_name (module : Module) (choices : ChoiceSchedule) (anchors used address : Nat)
    (heap : Mutable.Heap) (items : List Constant) (env : HeapCalls.Env) (target source : String)
    (body otherwise following : List Stmt) (stack : List HeapCalls.Frame)
    (lookup : env source = some (.ref address)) (found : heap[address]? = some (.set items)) :
    Reaches choices module anchors
      ⟨⟨.block (.forIn (.name target) (.name source) body otherwise :: following) env, stack, heap⟩, used⟩
      ⟨⟨.block (.setStepLoop target address items items body otherwise :: following) env, stack, heap⟩, used⟩ := by
  apply Reaches.next (following := ⟨⟨.expr (.name source) env,
    .sequence target body otherwise following env :: stack, heap⟩, used⟩) rfl
  apply (Reaches.of_heap (Evaluates.lookup lookup anchors _) choices used).trans
  exact .next (by simp [step, HeapCalls.step, HeapCalls.run, Mutable.sequence, found, iteratorStep, Mutable.unsupported]) .refl

/-- Any remaining representative can be chosen; the schedule is not a canonical ordering. -/
theorem select_item_mod (module : Module) (choices : ChoiceSchedule) (anchors used address index : Nat)
    (heap : Mutable.Heap) (original remaining : List Constant) (item : Constant)
    (env : HeapCalls.Env) (target : String) (body otherwise following : List Stmt) (stack : List HeapCalls.Frame)
    (found : heap[address]? = some (.set original)) (selected : remaining[index]? = some item)
    (choice : choices used % remaining.length = index) :
    step module anchors choices
      ⟨⟨.block (.setStepLoop target address original remaining body otherwise :: following) env, stack, heap⟩, used⟩ =
      .next ⟨⟨.block (body ++ [Calls.loopContinuation body
        (.setStepLoop target address original (remaining.eraseIdx index) body otherwise)] ++ following)
        (setLocal env target (.scalar item)), stack, heap⟩, used + 1⟩ := by
  cases remaining with
  | nil => simp at selected
  | cons head tail =>
    change choices used % (tail.length + 1) = index at choice
    simp [step, HeapCalls.step, iteratorStep, found, choice, selected]

theorem select_item (module : Module) (choices : ChoiceSchedule) (anchors used address index : Nat)
    (heap : Mutable.Heap) (original remaining : List Constant) (item : Constant)
    (env : HeapCalls.Env) (target : String) (body otherwise following : List Stmt) (stack : List HeapCalls.Frame)
    (found : heap[address]? = some (.set original)) (selected : remaining[index]? = some item)
    (choice : choices used = index) :
    step module anchors choices
      ⟨⟨.block (.setStepLoop target address original remaining body otherwise :: following) env, stack, heap⟩, used⟩ =
      .next ⟨⟨.block (body ++ [Calls.loopContinuation body
        (.setStepLoop target address original (remaining.eraseIdx index) body otherwise)] ++ following)
        (setLocal env target (.scalar item)), stack, heap⟩, used + 1⟩ := by
  exact select_item_mod module choices anchors used address index heap original remaining item env target
    body otherwise following stack found selected (by rw [choice]; exact Nat.mod_eq_of_lt (List.getElem?_eq_some_iff.mp selected).1)

end FormalSW.PyAst.SetCalls
