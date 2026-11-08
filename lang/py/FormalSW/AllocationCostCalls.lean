import lang.py.FormalSW.AllocationCost

/-! Compositional source-trace rules charging transitions and newly allocated list slots. -/
namespace FormalSW.PyAst.HeapCalls.AllocationCost.Calls
open Mutable

private theorem next (transition : step module anchors initial = .next following)
    (rest : ReachesWith (step module anchors) (charge module anchors) following cost final)
    (sameHeap : initial.heap = following.heap := by rfl) :
    ReachesWith (step module anchors) (charge module anchors) initial (cost + 1) final :=
  next_same_heap transition sameHeap rest

private theorem allocate (transition : step module anchors initial = .next following)
    (slots : listSlots following.heap = listSlots initial.heap + delta)
    (rest : ReachesWith (step module anchors) (charge module anchors) following cost final) :
    ReachesWith (step module anchors) (charge module anchors) initial (cost + delta + 1) final := by
  have weighted := ReachesWith.next (charge := charge module anchors) transition rest
  simpa [charge, transition, slots, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using weighted

def EvaluatesIn (module : Module) (env : Env) (expression : Expr)
    (heap : Heap) (cost : Nat) (value : Value) (finalHeap : Heap) : Prop :=
  ∀ anchors stack, ReachesWith (step module anchors) (charge module anchors)
    ⟨.expr expression env, stack, heap⟩ cost ⟨.value value, stack, finalHeap⟩

def ReturnsIn (module : Module) (name : String) (values : List Value)
    (heap : Heap) (cost : Nat) (value : Value) (finalHeap : Heap) : Prop :=
  ∀ anchors stack, ReachesWith (step module anchors) (charge module anchors)
    ⟨.operation (.call name) values, stack, heap⟩ cost ⟨.value value, stack, finalHeap⟩

def BlockReturnsIn (module : Module) (env : Env) (body : List Stmt)
    (heap : Heap) (cost : Nat) (value : Value) (finalHeap : Heap) : Prop :=
  ∀ anchors stack, ReachesWith (step module anchors) (charge module anchors)
    ⟨.block body env, stack, heap⟩ cost ⟨.value value, stack, finalHeap⟩

theorem ReturnsIn.timeBound (h : ReturnsIn module name values heap cost value finalHeap) :
    (HeapCalls.call module name values heap).execution.WeightedTimeBound
      (charge module heap.length) (cost + 1) :=
  ⟨cost + 1, _, (h heap.length []).finishes (finish_value _ _ _ _), Nat.le_refl _⟩

namespace EvaluatesIn

theorem constant : EvaluatesIn module env (.constant value) heap 1 (.scalar value) heap :=
  fun _ _ => next rfl .refl

theorem lookup (found : env name = some value) :
    EvaluatesIn module env (.name name) heap 1 value heap :=
  fun _ _ => next (by simp [step, found]) .refl

theorem binary (left : EvaluatesIn module env a heap ca av middle)
    (right : EvaluatesIn module env b middle cb bv afterRight)
    (operation : Mutable.binary op av bv afterRight = some (.ok value, finalHeap))
    (slots : listSlots finalHeap = listSlots afterRight + delta) :
    EvaluatesIn module env (.binOp a op b) heap (ca + cb + delta + 3) value finalHeap := by
  intro anchors stack
  have run := next (module := module) (anchors := anchors)
    (initial := ⟨.expr (.binOp a op b) env, stack, heap⟩) rfl
    ((left anchors _).trans (next rfl ((right anchors _).trans
      (allocate (following := ⟨.value value, stack, finalHeap⟩)
        (by simp [step, result, HeapCalls.run, operation]) slots .refl))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem unary (evaluated : EvaluatesIn module env expression heap cost value middle)
    (operation : HeapCalls.unary op value middle = some (.ok answer, middle)) :
    EvaluatesIn module env (.unaryOp op expression) heap (cost + 2) answer middle := by
  intro anchors stack
  exact next rfl ((evaluated anchors _).trans
    (next (by simp [step, result, run, operation]) .refl))

theorem compare (left : EvaluatesIn module env a heap ca av middle)
    (right : EvaluatesIn module env b middle cb bv afterRight)
    (operation : HeapCalls.compare op av bv afterRight = some (.ok value, afterRight)) :
    EvaluatesIn module env (.compare a [(op, b)]) heap (ca + cb + 3) value afterRight := by
  intro anchors stack
  have run := next (module := module) (anchors := anchors)
    (initial := ⟨.expr (.compare a [(op, b)]) env, stack, heap⟩) rfl
    ((left anchors _).trans (next rfl ((right anchors _).trans
      (next (following := ⟨.value value, stack, afterRight⟩)
        (by simp [step, result, HeapCalls.run, operation]) .refl))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

inductive Arguments (module : Module) (env : Env) : List Expr → Heap → Nat → List Value → Heap → Prop where
  | nil : Arguments module env [] heap 0 [] heap
  | cons : EvaluatesIn module env expression heap headCost value middle →
      Arguments module env expressions middle tailCost values finalHeap →
      Arguments module env (expression :: expressions) heap (headCost + tailCost + 1) (value :: values) finalHeap

theorem arguments_reach (h : Arguments module env expressions heap cost values finalHeap)
    (operation : Operation) (done : List Value) (anchors : Nat) (stack : List Frame) :
    ReachesWith (step module anchors) (charge module anchors)
      (argumentsState operation env done expressions stack heap) cost
      ⟨.operation operation (done ++ values), stack, finalHeap⟩ := by
  induction h generalizing done with
  | nil => simp [argumentsState]; exact .refl
  | @cons expression heap headCost value middle expressions tailCost values finalHeap head tail ih =>
      have run := (head anchors (.arguments operation done expressions env :: stack)).trans
        (next rfl (ih (done ++ [value])) (by cases expressions <;> rfl))
      simpa [argumentsState, List.append_assoc, Nat.add_assoc] using run

theorem call (arguments : Arguments module env expressions heap ca values middle)
    (callee : ReturnsIn module name values middle cc value finalHeap) :
    EvaluatesIn module env (.call (.name name) expressions) heap (ca + cc + 1) value finalHeap :=
  fun anchors stack => next rfl
    ((arguments_reach arguments (.call name) [] anchors stack).trans (callee anchors stack)) (by cases expressions <;> rfl)

theorem builtin (arguments : Arguments module env expressions heap cost values middle)
    (operation : primitive (.builtin name) values middle = some (.ok value, middle)) :
    EvaluatesIn module env (.builtinCall name expressions) heap (cost + 2) value middle := by
  intro anchors stack
  refine next (following := argumentsState (.builtin name) env [] expressions stack heap) rfl ?_ (by cases expressions <;> rfl)
  apply (arguments_reach arguments (.builtin name) [] anchors stack).trans
  cases name with
  | all | any => simp [primitive, Mutable.unsupported] at operation
  | _ => exact next (by simp [step, result, run, operation]) .refl

theorem list (arguments : Arguments module env expressions heap cost values finalHeap) :
    EvaluatesIn module env (.list expressions) heap (cost + values.length + 2) (.ref finalHeap.length)
      (finalHeap ++ [.list values]) := by
  intro anchors stack
  have run := next (module := module) (anchors := anchors)
    (initial := ⟨.expr (.list expressions) env, stack, heap⟩) rfl
    ((arguments_reach arguments .list [] anchors stack).trans
      (allocate (delta := values.length) (following := ⟨.value (.ref finalHeap.length), stack, finalHeap ++ [.list values]⟩)
        (by simp [step, result, HeapCalls.run, primitive, Mutable.allocate, Except.map])
        (by simp) .refl)) (by cases expressions <;> rfl)
  simpa [Nat.add_assoc] using run

theorem slice (arguments : Arguments module env
    [base, lower.getD (.constant .none), upper.getD (.constant .none), stride.getD (.constant .none)]
    heap cost [receiver, first, last, stepValue] middle)
    (operation : Mutable.getSlice receiver first last stepValue middle = some (.ok value, finalHeap))
    (slots : listSlots finalHeap = listSlots middle + delta) :
    EvaluatesIn module env (.subscript base (.slice lower upper stride)) heap
      (cost + delta + 2) value finalHeap := by
  intro anchors stack
  have run := next (module := module) (anchors := anchors)
    (initial := ⟨.expr (.subscript base (.slice lower upper stride)) env, stack, heap⟩) rfl
    ((arguments_reach arguments .slice [] anchors stack).trans
      (allocate (following := ⟨.value value, stack, finalHeap⟩)
        (by simp [step, primitive, result, HeapCalls.run, operation]) slots .refl))
  simpa [Nat.add_assoc] using run

end EvaluatesIn

namespace BlockReturnsIn

theorem branch (evaluated : EvaluatesIn module env condition heap cc value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockReturnsIn module env ((if flag then yes else no) ++ body) middle cb answer finalHeap) :
    BlockReturnsIn module env (.ifThen condition yes no :: body) heap (cc + (cb + 1) + 1) answer finalHeap :=
  fun anchors stack => next rfl ((evaluated anchors _).trans
    (next (by simp [step, run, truth]) (rest anchors stack)))

theorem return_value (evaluated : EvaluatesIn module env expression heap cost value finalHeap) :
    BlockReturnsIn module env (.return expression :: following) heap (cost + 1) value finalHeap :=
  fun anchors stack => next rfl (evaluated anchors stack)

theorem assign (evaluated : EvaluatesIn module env expression heap ca value middle)
    (rest : BlockReturnsIn module (setLocal env name value) following middle cb answer finalHeap) :
    BlockReturnsIn module env (.assign [.name name] expression :: following) heap (ca + cb + 2) answer finalHeap := by
  intro anchors stack
  have run := next (module := module) (anchors := anchors)
    (initial := ⟨.block (.assign [.name name] expression :: following) env, stack, heap⟩)
    rfl ((evaluated anchors _).trans (next rfl (rest anchors stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem function (found : findFunctionIn module.body name = some (args, body))
    (arity : completeArguments args values = some completed)
    (evaluated : BlockReturnsIn module (functionEnv args body completed []) (executableBody body) heap cost value finalHeap) :
    ReturnsIn module name values heap (cost + 1) value finalHeap :=
  fun anchors stack => next (by simp [step, found, arity]) (evaluated anchors stack)

theorem for_sequence_name (found : env iterable = some value)
    (sequence : Mutable.sequence value heap = some (.ok items, heap))
    (rest : BlockReturnsIn module env
      (.sequenceStepLoop name (sequenceSource value) 0 body otherwise :: following) heap cost answer finalHeap) :
    BlockReturnsIn module env (.forIn (.name name) (.name iterable) body otherwise :: following)
      heap (cost + 3) answer finalHeap := by
  intro anchors stack
  have run := next (module := module) (anchors := anchors)
    (initial := ⟨.block (.forIn (.name name) (.name iterable) body otherwise :: following) env, stack, heap⟩)
    rfl ((EvaluatesIn.lookup (module := module) (heap := heap) found anchors (.sequence name body otherwise following env :: stack)).trans
    (next (by simp [step, HeapCalls.run, sequence]) (rest anchors stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem sequence_step (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (rest : BlockReturnsIn module (setLocal env name value)
      (body ++ [FormalSW.PyAst.Calls.loopContinuation body (.sequenceStepLoop name source (position + 1) body otherwise)] ++ following)
      heap cost answer finalHeap) :
    BlockReturnsIn module env (.sequenceStepLoop name source position body otherwise :: following)
      heap (cost + 1) answer finalHeap :=
  fun anchors stack => next (by simp [step, run, sequence, item]) (rest anchors stack)

theorem sequence_done (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (finished : items[position]? = none)
    (rest : BlockReturnsIn module env (otherwise ++ following) heap cost answer finalHeap) :
    BlockReturnsIn module env (.sequenceStepLoop name source position body otherwise :: following)
      heap (cost + 1) answer finalHeap :=
  fun anchors stack => next (by simp [step, run, sequence, finished]) (rest anchors stack)

theorem augAssign (lookup : env name = some left)
    (evaluated : EvaluatesIn module env expression heap ca right middle)
    (operation : inplace op left right middle = some (.ok value, middle))
    (rest : BlockReturnsIn module (setLocal env name value) body middle cb answer finalHeap) :
    BlockReturnsIn module env (.augAssign (.name name) op expression :: body) heap (ca + cb + 5) answer finalHeap := by
  intro anchors stack
  have run := next (module := module) (anchors := anchors)
    (initial := ⟨.block (.augAssign (.name name) op expression :: body) env, stack, heap⟩)
    rfl ((EvaluatesIn.lookup (module := module) (heap := heap) lookup anchors _).trans
      (next rfl ((evaluated anchors _).trans
        (next (following := ⟨.value value, .assign name body env :: stack, middle⟩)
          (by simp [step, result, HeapCalls.run, operation]) (next rfl (rest anchors stack))))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end BlockReturnsIn
end FormalSW.PyAst.HeapCalls.AllocationCost.Calls
