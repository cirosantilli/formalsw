import lang.py.FormalSW.AllocationCost

/-! Compositional weighted execution rules for heap-preserving expressions and
statements. Every rule follows the actual heap interpreter; no copied list work
is hidden behind a scalar charge. Primitive premises require an unchanged heap. -/
namespace FormalSW.PyAst.HeapCalls.AllocationCost.ReadOnly

@[simp] theorem argumentsState_heap (operation : Operation) (env : Env) (done : List Value)
    (expressions : List Expr) (stack : List Frame) (heap : Heap) :
    (argumentsState operation env done expressions stack heap).heap = heap := by
  cases expressions <;> rfl

/-- A transition preserving the heap pays one unit. -/
theorem unitStep (transition : step module anchors state = .next following)
    (rest : ReachesWith (step module anchors) (charge module anchors) following cost final)
    (sameHeap : state.heap = following.heap := by simp) :
    ReachesWith (step module anchors) (charge module anchors) state (cost + 1) final :=
  next_same_heap transition sameHeap rest

def EvaluatesIn (module : Module) (env : Env) (expression : Expr)
    (heap : Heap) (cost : Nat) (value : Value) (finalHeap : Heap)
    : Prop :=
  ∀ anchors stack, ReachesWith (step module anchors) (charge module anchors)
    ⟨.expr expression env, stack, heap⟩ cost ⟨.value value, stack, finalHeap⟩

def ReturnsIn (module : Module) (name : String) (values : List Value)
    (heap : Heap) (cost : Nat) (value : Value) (finalHeap : Heap)
    : Prop :=
  ∀ anchors stack, ReachesWith (step module anchors) (charge module anchors)
    ⟨.operation (.call name) values, stack, heap⟩ cost ⟨.value value, stack, finalHeap⟩

def BlockContinuesIn (module : Module) (env : Env) (body : List Stmt)
    (heap : Heap) (cost : Nat) (finalEnv : Env) (finalHeap : Heap)
    : Prop :=
  ∀ following anchors stack, ReachesWith (step module anchors) (charge module anchors)
    ⟨.block (body ++ following) env, stack, heap⟩ cost
    ⟨.block following finalEnv, stack, finalHeap⟩

def BlockReturnsIn (module : Module) (env : Env) (body : List Stmt)
    (heap : Heap) (cost : Nat) (value : Value) (finalHeap : Heap)
    : Prop :=
  ∀ anchors stack, ReachesWith (step module anchors) (charge module anchors)
    ⟨.block body env, stack, heap⟩ cost ⟨.value value, stack, finalHeap⟩

namespace EvaluatesIn

theorem constant : EvaluatesIn module env (.constant value) heap 1 (.scalar value) heap :=
  fun _ _ => unitStep rfl .refl

theorem lookup (found : env name = some value) :
    EvaluatesIn module env (.name name) heap 1 value heap :=
  fun _ _ => unitStep (by simp [step, found]) .refl

theorem binary (left : EvaluatesIn module env a heap ca av heap)
    (right : EvaluatesIn module env b heap cb bv heap)
    (operation : Mutable.binary op av bv heap = some (.ok value, heap)) :
    EvaluatesIn module env (.binOp a op b) heap (ca + cb + 3) value heap := by
  intro anchors stack
  have run := unitStep (state := ⟨.expr (.binOp a op b) env, stack, heap⟩) rfl
    ((left anchors _).trans (unitStep rfl ((right anchors _).trans
      (unitStep (following := ⟨.value value, stack, heap⟩) (by simp [step, result, HeapCalls.run, operation]) .refl))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem unary (evaluated : EvaluatesIn module env expression heap cost value heap)
    (operation : HeapCalls.unary op value heap = some (.ok answer, heap)) :
    EvaluatesIn module env (.unaryOp op expression) heap (cost + 2) answer heap := by
  intro anchors stack
  exact unitStep rfl ((evaluated anchors _).trans
    (unitStep (by simp [step, result, run, operation]) .refl))

theorem compare (left : EvaluatesIn module env a heap ca av heap)
    (right : EvaluatesIn module env b heap cb bv heap)
    (operation : HeapCalls.compare op av bv heap = some (.ok value, heap)) :
    EvaluatesIn module env (.compare a [(op, b)]) heap (ca + cb + 3) value heap := by
  intro anchors stack
  have run := unitStep (state := ⟨.expr (.compare a [(op, b)]) env, stack, heap⟩) rfl
    ((left anchors _).trans (unitStep rfl ((right anchors _).trans
      (unitStep (following := ⟨.value value, stack, heap⟩) (by simp [step, result, HeapCalls.run, operation]) .refl))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem conditional (condition : EvaluatesIn module env test heap ct value heap)
    (truth : Mutable.truth value heap = some (.ok flag, heap))
    (branch : EvaluatesIn module env (if flag then yes else no) heap cb answer heap) :
    EvaluatesIn module env (.ifExp test yes no) heap (ct + cb + 2) answer heap := by
  intro anchors stack
  have run := unitStep (state := ⟨.expr (.ifExp test yes no) env, stack, heap⟩) rfl
    ((condition anchors _).trans (unitStep (by simp [step, HeapCalls.run, truth]) (branch anchors stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

inductive Arguments (module : Module) (env : Env) :
    List Expr → Heap → Nat → List Value → Heap → Prop where
  | nil : Arguments module env [] heap 0 [] heap
  | cons :
      EvaluatesIn module env expression heap headCost value heap →
      Arguments module env expressions heap tailCost values heap →
      Arguments module env (expression :: expressions) heap
        (headCost + tailCost + 1) (value :: values) heap

theorem arguments_reach (h : Arguments module env expressions heap cost values finalHeap)
    (operation : Operation) (done : List Value) (anchors : Nat) (stack : List Frame) :
    ReachesWith (step module anchors) (charge module anchors)
      (argumentsState operation env done expressions stack heap) cost
      ⟨.operation operation (done ++ values), stack, finalHeap⟩ := by
  induction h generalizing done with
  | nil => simp [argumentsState]; exact .refl
  | @cons expression heap headCost value expressions tailCost values head tail ih =>
      have run := (head anchors (.arguments operation done expressions env :: stack)).trans
        (unitStep rfl (ih (done ++ [value])) (by cases expressions <;> rfl))
      simpa [argumentsState, List.append_assoc, Nat.add_assoc] using run

theorem call (arguments : Arguments module env expressions heap ca values heap)
    (callee : ReturnsIn module name values heap cc value heap) :
    EvaluatesIn module env (.call (.name name) expressions) heap (ca + cc + 1) value heap :=
  fun anchors stack => unitStep rfl ((arguments_reach arguments (.call name) [] anchors stack).trans (callee anchors stack))

theorem builtin (arguments : Arguments module env expressions heap cost values heap)
    (operation : primitive (.builtin name) values heap = some (.ok value, heap)) :
    EvaluatesIn module env (.builtinCall name expressions) heap (cost + 2) value heap := by
  intro anchors stack
  refine unitStep (following := argumentsState (.builtin name) env [] expressions stack heap) rfl ?_
  apply (arguments_reach arguments (.builtin name) [] anchors stack).trans
  cases name with
  | all | any => simp [primitive, Mutable.unsupported] at operation
  | _ => exact unitStep (by simp [step, result, run, operation]) .refl

theorem subscript {index : Expr} (ordinary : ∀ a b c, index ≠ .slice a b c)
    (receiver : EvaluatesIn module env base heap cr value heap)
    (subscript : EvaluatesIn module env index heap ci position heap)
    (operation : Mutable.getItem value position heap = some (.ok answer, heap)) :
    EvaluatesIn module env (.subscript base index) heap
      (cr + (ci + 2 + 1) + 1) answer heap := by
  intro anchors stack
  have start : step module anchors ⟨.expr (.subscript base index) env, stack, heap⟩ =
      .next ⟨.expr base env, .arguments .subscript [] [index] env :: stack, heap⟩ := by
    cases index <;> simp_all [step, argumentsState]
  exact unitStep start ((receiver anchors _).trans (unitStep rfl ((subscript anchors _).trans
    (unitStep rfl (unitStep (by simp [argumentsState, step, primitive, result, run, operation]) .refl)))))

theorem boolean_stop (evaluated : EvaluatesIn module env first heap cost value heap)
    (truth : Mutable.truth value heap = some (.ok flag, heap))
    (stop : (match op with | .and => !flag | .or => flag) = true) :
    EvaluatesIn module env (.boolOp op (first :: rest)) heap (cost + 2) value heap :=
  fun anchors stack => unitStep rfl ((evaluated anchors _).trans
    (unitStep (by cases op <;> cases flag <;> simp_all only [Bool.not_true, Bool.not_false, Bool.false_eq_true]; all_goals simp [step, run, truth]) .refl))

theorem boolean_last (evaluated : EvaluatesIn module env expression heap cost value heap)
    (truth : Mutable.truth value heap = some (.ok flag, heap)) :
    EvaluatesIn module env (.boolOp op [expression]) heap (cost + 2) value heap := by
  intro anchors stack
  refine unitStep rfl ((evaluated anchors _).trans (unitStep ?_ .refl))
  cases op <;> cases flag <;> simp [step, run, truth]

/-- A two-operand Boolean expression, including short-circuit control work. -/
theorem boolean_pair (left : EvaluatesIn module env first heap ca value heap)
    (truth : Mutable.truth value heap = some (.ok flag, heap))
    (continues : (match op with | .and => !flag | .or => flag) = false)
    (right : EvaluatesIn module env second heap cb answer heap)
    (answerTruth : Mutable.truth answer heap = some (.ok answerFlag, heap)) :
    EvaluatesIn module env (.boolOp op [first, second]) heap (ca + cb + 3) answer heap := by
  intro anchors stack
  have run := unitStep (state := ⟨.expr (.boolOp op [first, second]) env, stack, heap⟩) rfl
    ((left anchors (.boolean op [second] env :: stack)).trans (unitStep
      (by cases op <;> cases flag <;> simp_all only [Bool.not_true, Bool.not_false, Bool.true_eq_false]
          all_goals simp [step, HeapCalls.run, truth])
      ((right anchors (.boolean op [] env :: stack)).trans
        (unitStep (following := ⟨.value answer, stack, heap⟩)
          (by cases op <;> cases answerFlag <;> simp [step, HeapCalls.run, answerTruth]) .refl))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end EvaluatesIn

private def rangeState (name : String) (env : Env) (done : List Value)
    (expressions : List Expr) (body otherwise following : List Stmt)
    (stack : List Frame) (heap : Heap) : State :=
  match expressions with
  | [] => ⟨.startRange name done body otherwise following env, stack, heap⟩
  | first :: rest =>
      ⟨.expr first env, .rangeArguments name done rest body otherwise following env :: stack, heap⟩

@[simp] private theorem rangeState_heap (name : String) (env : Env) (done : List Value)
    (expressions : List Expr) (body otherwise following : List Stmt)
    (stack : List Frame) (heap : Heap) :
    (rangeState name env done expressions body otherwise following stack heap).heap = heap := by
  cases expressions <;> rfl

private theorem range_reach
    (h : EvaluatesIn.Arguments module env expressions heap cost values finalHeap)
    (done : List Value) (anchors : Nat) (stack : List Frame) :
    ReachesWith (step module anchors) (charge module anchors)
      (rangeState name env done expressions body otherwise following stack heap) cost
      ⟨.startRange name (done ++ values) body otherwise following env, stack, finalHeap⟩ := by
  induction h generalizing done with
  | nil => simp [rangeState]; exact .refl
  | @cons expression heap headCost value expressions tailCost values head tail ih =>
      have run := (head anchors (.rangeArguments name done expressions body otherwise following env :: stack)).trans
        (unitStep rfl (ih (done ++ [value])) (by cases expressions <;> rfl))
      simpa [rangeState, List.append_assoc, Nat.add_assoc] using run

namespace BlockContinuesIn

theorem for_range (arguments : EvaluatesIn.Arguments module env expressions heap ca values heap)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (executed : BlockContinuesIn module env [.rangeStepLoop name start stop stride body otherwise]
      heap cb finalEnv heap) :
    BlockContinuesIn module env [.forIn (.name name) (.call (.name "range") expressions) body otherwise]
      heap (ca + (cb + 1) + 1) finalEnv heap := by
  intro following anchors stack
  exact unitStep (sameHeap := by cases expressions <;> rfl) rfl ((range_reach arguments [] anchors stack).trans
    (unitStep (by simp [step, bounds]) (executed following anchors stack)))

theorem augAssign (lookup : env name = some left)
    (evaluated : EvaluatesIn module env expression heap cost right heap)
    (operation : inplace op left right heap = some (.ok value, heap)) :
    BlockContinuesIn module env [.augAssign (.name name) op expression] heap
      (1 + (cost + 2 + 1) + 1) (setLocal env name value) heap := by
  intro following anchors stack
  refine unitStep rfl ((EvaluatesIn.lookup (module := module) (heap := heap) lookup anchors _).trans (unitStep rfl ?_))
  exact (evaluated anchors _).trans (unitStep
    (following := ⟨.value value, .assign name following env :: stack, heap⟩)
    (by simp [step, result, run, operation]) (unitStep rfl .refl))

theorem nil : BlockContinuesIn module env [] heap 0 env heap := fun _ _ _ => .refl

theorem append (first : BlockContinuesIn module env body heap ca middleEnv heap)
    (second : BlockContinuesIn module middleEnv rest heap cb finalEnv heap) :
    BlockContinuesIn module env (body ++ rest) heap (ca + cb) finalEnv heap := by
  intro following anchors stack
  simpa only [List.append_assoc] using
    (first (rest ++ following) anchors stack).trans (second following anchors stack)

theorem assign (evaluated : EvaluatesIn module env expression heap cost value heap) :
    BlockContinuesIn module env [.assign [.name name] expression] heap
      (cost + 2) (setLocal env name value) heap :=
  fun _ anchors _ => unitStep rfl ((evaluated anchors _).trans (unitStep rfl .refl))

theorem unpack (targets : Calls.targetNames expressions = some names)
    (evaluated : EvaluatesIn module env expression heap cost value heap)
    (sequence : Mutable.sequence value heap = some (.ok items, heap))
    (arity : names.length = items.length) :
    BlockContinuesIn module env [.assign [.tuple expressions] expression] heap
      (cost + 2) (assignNames env names items) heap := by
  intro following anchors stack
  exact unitStep (following := ⟨.expr expression env, .unpack names following env :: stack, heap⟩)
    (by simp [step, targets]) ((evaluated anchors _).trans
    (unitStep (by simp [step, run, sequence, arity]) .refl))

theorem discard (evaluated : EvaluatesIn module env expression heap cost value heap) :
    BlockContinuesIn module env [.expr expression] heap (cost + 2) env heap :=
  fun _ anchors _ => unitStep rfl ((evaluated anchors _).trans (unitStep rfl .refl))

theorem branch (evaluated : EvaluatesIn module env condition heap cc value heap)
    (truth : Mutable.truth value heap = some (.ok flag, heap))
    (body : BlockContinuesIn module env (if flag then yes else no) heap cb finalEnv heap) :
    BlockContinuesIn module env [.ifThen condition yes no] heap (cc + cb + 2) finalEnv heap := by
  intro following anchors stack
  have run := unitStep (state := ⟨.block ([.ifThen condition yes no] ++ following) env, stack, heap⟩) rfl
    ((evaluated anchors _).trans (unitStep (by simp [step, HeapCalls.run, truth]) (body following anchors stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem while_loop (evaluated : EvaluatesIn module env condition heap cc value heap)
    (truth : Mutable.truth value heap = some (.ok flag, heap))
    (rest : BlockContinuesIn module env
      (if flag then body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)] else otherwise)
      heap cb finalEnv heap) :
    BlockContinuesIn module env [.whileDo condition body otherwise] heap (cc + cb + 2) finalEnv heap := by
  intro following anchors stack
  have run := unitStep (state := ⟨.block ([.whileDo condition body otherwise] ++ following) env, stack, heap⟩) rfl
    ((evaluated anchors _).trans (unitStep (by simp [step, HeapCalls.run, truth]) (rest following anchors stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem range_step (continues : Calls.rangeContinues next stop stride = true)
    (rest : BlockContinuesIn module (setLocal env name (.scalar (.int next)))
      (body ++ [Calls.loopContinuation body (.rangeStepLoop name (next + stride) stop stride body otherwise)])
      heap cost finalEnv heap) :
    BlockContinuesIn module env [.rangeStepLoop name next stop stride body otherwise]
      heap (cost + 1) finalEnv heap := by
  intro following anchors stack
  refine unitStep ?_ (rest following anchors stack)
  simp [step, continues, List.append_assoc]

theorem range_done (finished : Calls.rangeContinues next stop stride = false)
    (rest : BlockContinuesIn module env otherwise heap cost finalEnv heap) :
    BlockContinuesIn module env [.rangeStepLoop name next stop stride body otherwise]
      heap (cost + 1) finalEnv heap :=
  fun following anchors stack => unitStep (by simp [step, finished]) (rest following anchors stack)

theorem loop_resume (rest : BlockContinuesIn module env [next] heap cost finalEnv heap) :
    BlockContinuesIn module env [.loopResume next] heap (cost + 1) finalEnv heap :=
  fun following anchors stack => unitStep rfl (rest following anchors stack)

theorem returns (first : BlockContinuesIn module env body heap ca middleEnv heap)
    (rest : BlockReturnsIn module middleEnv following heap cb answer heap) :
    BlockReturnsIn module env (body ++ following) heap (ca + cb) answer heap :=
  fun anchors stack => (first following anchors stack).trans (rest anchors stack)

end BlockContinuesIn

namespace BlockReturnsIn

theorem branch (evaluated : EvaluatesIn module env condition heap cc value heap)
    (truth : Mutable.truth value heap = some (.ok flag, heap))
    (rest : BlockReturnsIn module env ((if flag then yes else no) ++ body)
      heap cb answer heap) :
    BlockReturnsIn module env (.ifThen condition yes no :: body) heap
      (cc + (cb + 1) + 1) answer heap :=
  fun anchors stack => unitStep rfl ((evaluated anchors _).trans
    (unitStep (by simp [step, run, truth]) (rest anchors stack)))

theorem while_loop (evaluated : EvaluatesIn module env condition heap cc value heap)
    (truth : Mutable.truth value heap = some (.ok flag, heap))
    (rest : BlockReturnsIn module env
      ((if flag then body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)] else otherwise) ++ following)
      heap cb answer heap) :
    BlockReturnsIn module env (.whileDo condition body otherwise :: following) heap
      (cc + (cb + 1) + 1) answer heap :=
  fun anchors stack => unitStep rfl ((evaluated anchors _).trans
    (unitStep (by simp [step, run, truth]) (rest anchors stack)))

theorem loop_resume (rest : BlockReturnsIn module env (next :: following) heap cost answer heap) :
    BlockReturnsIn module env (.loopResume next :: following) heap (cost + 1) answer heap :=
  fun anchors stack => unitStep rfl (rest anchors stack)

theorem break_loop (target : Calls.loopTarget body = some (next, following))
    (rest : BlockReturnsIn module env following heap cost answer heap) :
    BlockReturnsIn module env (.breakLoop :: body) heap (cost + 1) answer heap :=
  fun anchors stack => unitStep (by simp [step, target]) (rest anchors stack)

theorem continue_loop (target : Calls.loopTarget body = some (next, following))
    (rest : BlockReturnsIn module env (next :: following) heap cost answer heap) :
    BlockReturnsIn module env (.continueLoop :: body) heap (cost + 1) answer heap :=
  fun anchors stack => unitStep (by simp [step, target]) (rest anchors stack)

theorem for_range (arguments : EvaluatesIn.Arguments module env expressions heap ca values heap)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (rest : BlockReturnsIn module env (.rangeStepLoop name start stop stride body otherwise :: following)
      heap cb answer heap) :
    BlockReturnsIn module env (.forIn (.name name) (.call (.name "range") expressions) body otherwise :: following)
      heap (ca + (cb + 1) + 1) answer heap := by
  intro anchors stack
  exact unitStep (sameHeap := by cases expressions <;> rfl) rfl ((range_reach arguments [] anchors stack).trans
    (unitStep (by simp [step, bounds]) (rest anchors stack)))

theorem return_value (evaluated : EvaluatesIn module env expression heap cost value heap) :
    BlockReturnsIn module env (.return expression :: following) heap (cost + 1) value heap :=
  fun anchors stack => unitStep rfl (evaluated anchors stack)

theorem assign (evaluated : EvaluatesIn module env expression heap ca value heap)
    (rest : BlockReturnsIn module (setLocal env name value) following heap cb answer heap) :
    BlockReturnsIn module env (.assign [.name name] expression :: following) heap
      (ca + cb + 2) answer heap := by
  intro anchors stack
  have run := unitStep (state := ⟨.block (.assign [.name name] expression :: following) env, stack, heap⟩)
    rfl ((evaluated anchors _).trans (unitStep rfl (rest anchors stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem function (found : findFunctionIn module.body name = some (args, body))
    (arity : completeArguments args values = some completed)
    (evaluated : BlockReturnsIn module (functionEnv args body completed []) (executableBody body) heap cost value heap) :
    ReturnsIn module name values heap (cost + 1) value heap :=
  fun anchors stack => unitStep (by simp [step, found, arity]) (evaluated anchors stack)

end BlockReturnsIn

theorem ReturnsIn.timeBound (h : ReturnsIn module name values heap cost value finalHeap) :
    (HeapCalls.call module name values heap).execution.WeightedTimeBound
      (charge module heap.length) (cost + 1) :=
  ⟨cost + 1, _, (h heap.length []).finishes (finish_value module heap.length value finalHeap), Nat.le_refl _⟩

end FormalSW.PyAst.HeapCalls.AllocationCost.ReadOnly
