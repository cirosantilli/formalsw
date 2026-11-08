import lang.py.FormalSW.BufferCostSlice

/-! Compositional weighted execution rules for bytearray algorithms. -/
namespace FormalSW.PyAst.HeapCalls.BufferCost.Cost
open Mutable

@[simp] theorem argumentsState_heap (operation : Operation) (env : Env) (done : List Value)
    (expressions : List Expr) (stack : List Frame) (heap : Heap) :
    (argumentsState operation env done expressions stack heap).heap = heap := by
  cases expressions <;> rfl

/-- Ordinary control/evaluation steps have unit cost; byte work must be supplied separately. -/
theorem unitStep (transition : step module anchors state = .next following)
    (rest : ReachesWith (step module anchors) (charge module anchors) following cost final)
    (sameSlots : bufferSlots following.heap = bufferSlots state.heap := by simp)
    (noBytes : scalarBytes state following = 0 := by simp [scalarBytes, argumentsState])
    (noWrites : writtenBytes state following = 0 := by simp [writtenBytes, argumentsState]) :
    ReachesWith (step module anchors) (charge module anchors) state (cost + 1) final := by
  have charged : charge module anchors state = 1 := by
    simp [charge, transition, sameSlots, noBytes, noWrites]
  simpa only [charged, Nat.add_comm 1 cost] using ReachesWith.next transition rest

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

theorem binary (left : EvaluatesIn module env a heap ca av middle)
    (right : EvaluatesIn module env b middle cb bv afterRight)
    (operation : Mutable.binary op av bv afterRight = some (.ok (.scalar (.int value)), afterRight)) :
    EvaluatesIn module env (.binOp a op b) heap (ca + cb + 3) (.scalar (.int value)) afterRight := by
  intro anchors stack
  have run := unitStep (state := ⟨.expr (.binOp a op b) env, stack, heap⟩) rfl
    ((left anchors _).trans (unitStep rfl ((right anchors _).trans
      (unitStep (following := ⟨.value (.scalar (.int value)), stack, afterRight⟩) (by simp [step, result, HeapCalls.run, operation]) .refl))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem compare (left : EvaluatesIn module env a heap ca av middle)
    (right : EvaluatesIn module env b middle cb bv afterRight)
    (operation : HeapCalls.compare op av bv afterRight = some (.ok value, afterRight)) :
    EvaluatesIn module env (.compare a [(op, b)]) heap (ca + cb + 3) value afterRight := by
  intro anchors stack
  have run := unitStep (state := ⟨.expr (.compare a [(op, b)]) env, stack, heap⟩) rfl
    ((left anchors _).trans (unitStep rfl ((right anchors _).trans
      (unitStep (following := ⟨.value value, stack, afterRight⟩) (by simp [step, result, HeapCalls.run, operation]) .refl))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

inductive Arguments (module : Module) (env : Env) :
    List Expr → Heap → Nat → List Value → Heap → Prop where
  | nil : Arguments module env [] heap 0 [] heap
  | cons :
      EvaluatesIn module env expression heap headCost value middle →
      Arguments module env expressions middle tailCost values finalHeap →
      Arguments module env (expression :: expressions) heap
        (headCost + tailCost + 1) (value :: values) finalHeap

theorem arguments_reach (h : Arguments module env expressions heap cost values finalHeap)
    (operation : Operation) (done : List Value) (anchors : Nat) (stack : List Frame) :
    ReachesWith (step module anchors) (charge module anchors)
      (argumentsState operation env done expressions stack heap) cost
      ⟨.operation operation (done ++ values), stack, finalHeap⟩ := by
  induction h generalizing done with
  | nil => simp [argumentsState]; exact .refl
  | @cons expression heap headCost value middle expressions tailCost values finalHeap head tail ih =>
      have run := (head anchors (.arguments operation done expressions env :: stack)).trans
        (unitStep rfl (ih (done ++ [value])) (sameSlots := by cases expressions <;> rfl))
      simpa [argumentsState, List.append_assoc, Nat.add_assoc] using run

theorem call (arguments : Arguments module env expressions heap ca values middle)
    (callee : ReturnsIn module name values middle cc value finalHeap) :
    EvaluatesIn module env (.call (.name name) expressions) heap (ca + cc + 1) value finalHeap :=
  fun anchors stack => unitStep rfl ((arguments_reach arguments (.call name) [] anchors stack).trans (callee anchors stack))

theorem builtin (arguments : Arguments module env expressions heap cost values middle)
    (operation : primitive (.builtin name) values middle = some (.ok value, middle)) :
    EvaluatesIn module env (.builtinCall name expressions) heap (cost + 2) value middle := by
  intro anchors stack
  refine unitStep (following := argumentsState (.builtin name) env [] expressions stack heap) rfl ?_
  apply (arguments_reach arguments (.builtin name) [] anchors stack).trans
  cases name with
  | all | any => simp [primitive, Mutable.unsupported] at operation
  | _ => exact unitStep (by simp [step, result, run, operation]) .refl

theorem subscript {index : Expr} (ordinary : ∀ a b c, index ≠ .slice a b c)
    (receiver : EvaluatesIn module env base heap cr value middle)
    (subscript : EvaluatesIn module env index middle ci position afterIndex)
    (operation : Mutable.getItem value position afterIndex = some (.ok answer, afterIndex)) :
    EvaluatesIn module env (.subscript base index) heap
      (cr + (ci + 2 + 1) + 1) answer afterIndex := by
  intro anchors stack
  have start : step module anchors ⟨.expr (.subscript base index) env, stack, heap⟩ =
      .next ⟨.expr base env, .arguments .subscript [] [index] env :: stack, heap⟩ := by
    cases index <;> simp_all [step, argumentsState]
  exact unitStep start ((receiver anchors _).trans (unitStep rfl ((subscript anchors _).trans
    (unitStep rfl (unitStep (by simp [argumentsState, step, primitive, result, run, operation]) .refl)))))

end EvaluatesIn

private def rangeState (name : String) (env : Env) (done : List Value)
    (expressions : List Expr) (body otherwise following : List Stmt)
    (stack : List Frame) (heap : Heap) : State :=
  match expressions with
  | [] => ⟨.startRange name done body otherwise following env, stack, heap⟩
  | first :: rest =>
      ⟨.expr first env, .rangeArguments name done rest body otherwise following env :: stack, heap⟩

@[simp] theorem rangeState_heap (name : String) (env : Env) (done : List Value)
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
  | @cons expression heap headCost value middle expressions tailCost values finalHeap head tail ih =>
      have run := (head anchors (.rangeArguments name done expressions body otherwise following env :: stack)).trans
        (unitStep rfl (ih (done ++ [value])) (sameSlots := by cases expressions <;> rfl))
      simpa [rangeState, List.append_assoc, Nat.add_assoc] using run

namespace BlockContinuesIn

theorem for_range (arguments : EvaluatesIn.Arguments module env expressions heap ca values middle)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (executed : BlockContinuesIn module env [.rangeStepLoop name start stop stride body otherwise]
      middle cb finalEnv finalHeap) :
    BlockContinuesIn module env [.forIn (.name name) (.call (.name "range") expressions) body otherwise]
      heap (ca + (cb + 1) + 1) finalEnv finalHeap := by
  intro following anchors stack
  exact unitStep rfl ((range_reach arguments [] anchors stack).trans
    (unitStep (by simp [step, bounds]) (executed following anchors stack)))
    (sameSlots := by cases expressions <;> rfl)

theorem augAssign (lookup : env name = some left)
    (evaluated : EvaluatesIn module env expression heap cost right middle)
    (operation : inplace op left right middle = some (.ok (.scalar (.int value)), middle)) :
    BlockContinuesIn module env [.augAssign (.name name) op expression] heap
      (1 + (cost + 2 + 1) + 1) (setLocal env name (.scalar (.int value))) middle := by
  intro following anchors stack
  refine unitStep rfl ((EvaluatesIn.lookup (module := module) (heap := heap) lookup anchors _).trans (unitStep rfl ?_))
  exact (evaluated anchors _).trans (unitStep
    (following := ⟨.value (.scalar (.int value)), .assign name following env :: stack, middle⟩)
    (by simp [step, result, run, operation]) (unitStep rfl .refl))

theorem nil : BlockContinuesIn module env [] heap 0 env heap := fun _ _ _ => .refl

theorem append (first : BlockContinuesIn module env body heap ca middleEnv middleHeap)
    (second : BlockContinuesIn module middleEnv rest middleHeap cb finalEnv finalHeap) :
    BlockContinuesIn module env (body ++ rest) heap (ca + cb) finalEnv finalHeap := by
  intro following anchors stack
  simpa only [List.append_assoc] using
    (first (rest ++ following) anchors stack).trans (second following anchors stack)

theorem assign (evaluated : EvaluatesIn module env expression heap cost value finalHeap) :
    BlockContinuesIn module env [.assign [.name name] expression] heap
      (cost + 2) (setLocal env name value) finalHeap :=
  fun _ anchors _ => unitStep rfl ((evaluated anchors _).trans (unitStep rfl .refl))

theorem branch (evaluated : EvaluatesIn module env condition heap cc value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (body : BlockContinuesIn module env (if flag then yes else no) middle cb finalEnv finalHeap) :
    BlockContinuesIn module env [.ifThen condition yes no] heap (cc + cb + 2) finalEnv finalHeap := by
  intro following anchors stack
  have run := unitStep (state := ⟨.block ([.ifThen condition yes no] ++ following) env, stack, heap⟩) rfl
    ((evaluated anchors _).trans (unitStep (by simp [step, HeapCalls.run, truth]) (body following anchors stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem range_step (continues : Calls.rangeContinues next stop stride = true)
    (rest : BlockContinuesIn module (setLocal env name (.scalar (.int next)))
      (body ++ [Calls.loopContinuation body (.rangeStepLoop name (next + stride) stop stride body otherwise)])
      heap cost finalEnv finalHeap) :
    BlockContinuesIn module env [.rangeStepLoop name next stop stride body otherwise]
      heap (cost + 1) finalEnv finalHeap := by
  intro following anchors stack
  refine unitStep ?_ (rest following anchors stack)
  simp [step, continues, List.append_assoc]

theorem range_done (finished : Calls.rangeContinues next stop stride = false)
    (rest : BlockContinuesIn module env otherwise heap cost finalEnv finalHeap) :
    BlockContinuesIn module env [.rangeStepLoop name next stop stride body otherwise]
      heap (cost + 1) finalEnv finalHeap :=
  fun following anchors stack => unitStep (by simp [step, finished]) (rest following anchors stack)

theorem loop_resume (rest : BlockContinuesIn module env [next] heap cost finalEnv finalHeap) :
    BlockContinuesIn module env [.loopResume next] heap (cost + 1) finalEnv finalHeap :=
  fun following anchors stack => unitStep rfl (rest following anchors stack)

theorem returns (first : BlockContinuesIn module env body heap ca middleEnv middleHeap)
    (rest : BlockReturnsIn module middleEnv following middleHeap cb answer finalHeap) :
    BlockReturnsIn module env (body ++ following) heap (ca + cb) answer finalHeap :=
  fun anchors stack => (first following anchors stack).trans (rest anchors stack)

end BlockContinuesIn

namespace BlockReturnsIn

theorem branch (evaluated : EvaluatesIn module env condition heap cc value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockReturnsIn module env ((if flag then yes else no) ++ body)
      middle cb answer finalHeap) :
    BlockReturnsIn module env (.ifThen condition yes no :: body) heap
      (cc + (cb + 1) + 1) answer finalHeap :=
  fun anchors stack => unitStep rfl ((evaluated anchors _).trans
    (unitStep (by simp [step, run, truth]) (rest anchors stack)))

theorem return_value (evaluated : EvaluatesIn module env expression heap cost value finalHeap) :
    BlockReturnsIn module env (.return expression :: following) heap (cost + 1) value finalHeap :=
  fun anchors stack => unitStep rfl (evaluated anchors stack)

theorem assign (evaluated : EvaluatesIn module env expression heap ca value middle)
    (rest : BlockReturnsIn module (setLocal env name value) following middle cb answer finalHeap) :
    BlockReturnsIn module env (.assign [.name name] expression :: following) heap
      (ca + cb + 2) answer finalHeap := by
  intro anchors stack
  have run := unitStep (state := ⟨.block (.assign [.name name] expression :: following) env, stack, heap⟩)
    rfl ((evaluated anchors _).trans (unitStep rfl (rest anchors stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem function (found : findFunctionIn module.body name = some (args, body))
    (arity : completeArguments args values = some completed)
    (evaluated : BlockReturnsIn module (functionEnv args body completed []) (executableBody body) heap cost value finalHeap) :
    ReturnsIn module name values heap (cost + 1) value finalHeap :=
  fun anchors stack => unitStep (by simp [step, found, arity]) (evaluated anchors stack)

end BlockReturnsIn

end FormalSW.PyAst.HeapCalls.BufferCost.Cost
