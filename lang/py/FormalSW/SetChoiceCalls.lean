import lang.py.FormalSW.SetCalls

/-! Source-loop entry and an arbitrary permitted choice from a live set. -/
namespace FormalSW.PyAst.SetCalls
open HeapCalls
set_option Elab.async false

/-- The finite order selected by a schedule, consuming one choice per representative. -/
def selectionOrder {α : Type} (choices : ChoiceSchedule) (used : Nat) (items : List α) : List α :=
  match items with
  | [] => []
  | head :: tail =>
      let index := choices used % (head :: tail).length
      have bound : index < (head :: tail).length := Nat.mod_lt _ (by simp)
      (head :: tail)[index] :: selectionOrder choices (used + 1) ((head :: tail).eraseIdx index)
termination_by items.length
decreasing_by
  rw [List.length_eraseIdx_of_lt bound]
  simp

theorem selectionOrder_length {α : Type} (choices : ChoiceSchedule) (used : Nat) (items : List α) :
    (selectionOrder choices used items).length = items.length := by
  cases items with
  | nil => simp [selectionOrder]
  | cons head tail =>
      rw [selectionOrder, List.length_cons, selectionOrder_length]
      rw [List.length_eraseIdx_of_lt (Nat.mod_lt _ (by simp))]
      simp
termination_by items.length
decreasing_by
  rw [List.length_eraseIdx_of_lt (Nat.mod_lt _ (by simp))]
  simp

private theorem selected_erase_perm {α : Type} (items : List α) (index : Nat)
    (bound : index < items.length) : (items[index] :: items.eraseIdx index).Perm items := by
  induction items generalizing index with
  | nil => simp at bound
  | cons head tail ih =>
      cases index with
      | zero => exact .refl _
      | succ index =>
          have bounded : index < tail.length := Nat.lt_of_succ_lt_succ bound
          exact (List.Perm.swap head tail[index] _).trans ((ih index bounded).cons head)

/-- Traversal visits every representative exactly once, without assuming a particular order. -/
theorem selectionOrder_perm {α : Type} (choices : ChoiceSchedule) (used : Nat) (items : List α) :
    (selectionOrder choices used items).Perm items := by
  cases items with
  | nil => rw [selectionOrder]
  | cons head tail =>
      rw [selectionOrder]
      exact ((selectionOrder_perm choices (used + 1) _).cons _).trans
        (selected_erase_perm _ _ (Nat.mod_lt _ (by simp)))
termination_by items.length
decreasing_by
  rw [List.length_eraseIdx_of_lt (Nat.mod_lt _ (by simp))]
  simp

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

/-- Tuple-key traversal retains the original representatives, including their heap identities. -/
theorem for_key_set_name (module : Module) (choices : ChoiceSchedule) (anchors used address : Nat)
    (heap : Mutable.Heap) (items : List (HashKey × Mutable.Value)) (env : HeapCalls.Env) (target source : String)
    (body otherwise following : List Stmt) (stack : List HeapCalls.Frame)
    (lookup : env source = some (.ref address)) (found : heap[address]? = some (.keySet items)) :
    Reaches choices module anchors
      ⟨⟨.block (.forIn (.name target) (.name source) body otherwise :: following) env, stack, heap⟩, used⟩
      ⟨⟨.block (.keySetStepLoop target address items.length (items.map (fun item => sequenceSource item.2))
        body otherwise :: following) env, stack, heap⟩, used⟩ := by
  apply Reaches.next (following := ⟨⟨.expr (.name source) env,
    .sequence target body otherwise following env :: stack, heap⟩, used⟩) rfl
  apply (Reaches.of_heap (Evaluates.lookup lookup anchors _) choices used).trans
  exact .next (by simp [step, HeapCalls.step, HeapCalls.run, Mutable.sequence, found, iteratorStep, Mutable.unsupported]) .refl

/-- Unpacking retains a live source set and assigns fields before executing the body. -/
theorem unpack_key_set_start (module : Module) (choices : ChoiceSchedule) (anchors used address : Nat)
    (heap : Mutable.Heap) (items : List (HashKey × Mutable.Value)) (env : HeapCalls.Env) (names : List String)
    (body otherwise following : List Stmt) (stack : List HeapCalls.Frame)
    (found : heap[address]? = some (.keySet items)) :
    step module anchors choices
      ⟨⟨.value (.ref address), .unpackSequence names body otherwise following env :: stack, heap⟩, used⟩ =
      .next ⟨⟨.block (.keySetStepLoop "$formalsw.unpack" address items.length
        (items.map (fun item => sequenceSource item.2))
        (comprehensionTargetBody (.tuple (names.map Expr.name)) body) otherwise :: following) env, stack, heap⟩, used⟩ := by
  simp [step, HeapCalls.step, HeapCalls.run, Mutable.sequence, found, iteratorStep, Mutable.unsupported,
    Mutable.keyEntries]

/-- Any unvisited representative may be selected; tuple keys are never copied or canonicalized here. -/
theorem select_key_item_mod (module : Module) (choices : ChoiceSchedule) (anchors used address index : Nat)
    (heap : Mutable.Heap) (items : List (HashKey × Mutable.Value)) (remaining : List SequenceSource)
    (item : SequenceSource) (env : HeapCalls.Env) (target : String)
    (body otherwise following : List Stmt) (stack : List HeapCalls.Frame)
    (found : heap[address]? = some (.keySet items)) (selected : remaining[index]? = some item)
    (choice : choices used % remaining.length = index) :
    step module anchors choices
      ⟨⟨.block (.keySetStepLoop target address items.length remaining body otherwise :: following) env, stack, heap⟩, used⟩ =
      .next ⟨⟨.block (body ++ [Calls.loopContinuation body
        (.keySetStepLoop target address items.length (remaining.eraseIdx index) body otherwise)] ++ following)
        (setLocal env target (sequenceValue item)), stack, heap⟩, used + 1⟩ := by
  cases remaining with
  | nil => simp at selected
  | cons head tail =>
      change choices used % (tail.length + 1) = index at choice
      simp [step, HeapCalls.step, iteratorStep, Mutable.keyEntries, found, choice, selected]

theorem key_set_done (module : Module) (choices : ChoiceSchedule) (anchors used address : Nat)
    (heap : Mutable.Heap) (items : List (HashKey × Mutable.Value)) (env : HeapCalls.Env) (target : String)
    (body otherwise following : List Stmt) (stack : List HeapCalls.Frame)
    (found : heap[address]? = some (.keySet items)) :
    step module anchors choices
      ⟨⟨.block (.keySetStepLoop target address items.length [] body otherwise :: following) env, stack, heap⟩, used⟩ =
      .next ⟨⟨.block (otherwise ++ following) env, stack, heap⟩, used⟩ := by
  simp [step, HeapCalls.step, iteratorStep, Mutable.keyEntries, found]

end FormalSW.PyAst.SetCalls
