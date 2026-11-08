import lang.py.FormalSW.HeapCalls
import lang.py.FormalSW.ExecutionCost

/-! Compositional counts of actual heap-interpreter transitions.
These counts include control flow and allocation transitions, but do not assign
unit runtime to the collection traversals hidden inside a transition. A weighted
model must charge those operations separately. -/
namespace FormalSW.PyAst.HeapCalls

theorem Reaches.exists_cost (h : Reaches (globals := globals) module anchors initial final) :
    ∃ cost, ReachesIn (step (globals := globals) module anchors) initial cost final := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | next transition _ ih =>
      obtain ⟨cost, rest⟩ := ih
      exact ⟨cost + 1, .next transition rest⟩

namespace Cost
open Mutable

variable {globals : Mutable.Globals}

theorem reaches (h : ReachesIn (step (globals := globals) module anchors) initial cost final) :
    Reaches (globals := globals) module anchors initial final := by
  induction h with
  | refl => exact .refl
  | next transition _ ih => exact .next transition ih

theorem extend (h : ReachesIn (step (globals := globals) source anchors) initial cost final)
    (extension : Extends target source) :
    ReachesIn (step (globals := globals) target anchors) initial cost final := by
  induction h with
  | refl => exact .refl
  | next transition _ ih =>
      apply ReachesIn.next _ ih
      rw [step_extend extension _ (by simp [transition])]
      exact transition

def EvaluatesIn (module : Module) (env : Env) (expression : Expr)
    (heap : Heap) (cost : Nat) (value : Value) (finalHeap : Heap)
    (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, ReachesIn (step (globals := globals) module anchors)
    ⟨.expr expression env, stack, heap⟩ cost ⟨.value value, stack, finalHeap⟩

def ReturnsIn (module : Module) (name : String) (values : List Value)
    (heap : Heap) (cost : Nat) (value : Value) (finalHeap : Heap)
    (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, ReachesIn (step (globals := globals) module anchors)
    ⟨.operation (.call name) values, stack, heap⟩ cost ⟨.value value, stack, finalHeap⟩

def BlockContinuesIn (module : Module) (env : Env) (body : List Stmt)
    (heap : Heap) (cost : Nat) (finalEnv : Env) (finalHeap : Heap)
    (globals : Mutable.Globals := []) : Prop :=
  ∀ following anchors stack, ReachesIn (step (globals := globals) module anchors)
    ⟨.block (body ++ following) env, stack, heap⟩ cost
    ⟨.block following finalEnv, stack, finalHeap⟩

def BlockReturnsIn (module : Module) (env : Env) (body : List Stmt)
    (heap : Heap) (cost : Nat) (value : Value) (finalHeap : Heap)
    (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, ReachesIn (step (globals := globals) module anchors)
    ⟨.block body env, stack, heap⟩ cost ⟨.value value, stack, finalHeap⟩

theorem EvaluatesIn.evaluates (h : EvaluatesIn (globals := globals) module env expression heap cost value finalHeap) :
    Evaluates (globals := globals) module env expression heap value finalHeap :=
  fun anchors stack => reaches (h anchors stack)

theorem ReturnsIn.returnsValue (h : ReturnsIn (globals := globals) module name values heap cost value finalHeap) :
    ReturnsValue (globals := globals) module name values heap value finalHeap :=
  fun anchors stack => reaches (h anchors stack)

theorem ReturnsIn.extend (h : ReturnsIn (globals := globals) source name values heap cost value finalHeap)
    (extension : Extends target source) :
    ReturnsIn (globals := globals) target name values heap cost value finalHeap :=
  fun anchors stack => Cost.extend (h anchors stack) extension

theorem ReturnsIn.timeBound (h : ReturnsIn (globals := globals) module name values heap cost value finalHeap) :
    (HeapCalls.call (globals := globals) module name values heap).execution.TimeBound (cost + 1) :=
  ⟨cost + 1, _, (h heap.length []).finishes (.done rfl), Nat.le_refl _⟩

theorem BlockContinuesIn.continues
    (h : BlockContinuesIn (globals := globals) module env body heap cost finalEnv finalHeap) :
    BlockContinues (globals := globals) module env body heap finalEnv finalHeap :=
  fun following anchors stack => reaches (h following anchors stack)

theorem BlockReturnsIn.returns
    (h : BlockReturnsIn (globals := globals) module env body heap cost value finalHeap) :
    BlockReturns (globals := globals) module env body heap value finalHeap :=
  fun anchors stack => reaches (h anchors stack)

namespace EvaluatesIn

theorem constant : EvaluatesIn (globals := globals) module env (.constant value) heap 1 (.scalar value) heap :=
  fun _ _ => .next rfl .refl

theorem lookup (found : env name = some value) :
    EvaluatesIn (globals := globals) module env (.name name) heap 1 value heap :=
  fun _ _ => .next (by simp [step, found]) .refl

theorem binary (left : EvaluatesIn (globals := globals) module env a heap ca av middle)
    (right : EvaluatesIn (globals := globals) module env b middle cb bv afterRight)
    (operation : Mutable.binary op av bv afterRight = some (.ok value, finalHeap)) :
    EvaluatesIn (globals := globals) module env (.binOp a op b) heap (ca + cb + 3) value finalHeap := by
  intro anchors stack
  have run := ReachesIn.next (step := step (globals := globals) module anchors) (state := ⟨.expr (.binOp a op b) env, stack, heap⟩) rfl
    ((left anchors _).trans (.next rfl ((right anchors _).trans
      (.next (following := ⟨.value value, stack, finalHeap⟩) (by simp [step, result, HeapCalls.run, operation]) .refl))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem unary (evaluated : EvaluatesIn (globals := globals) module env expression heap cost value middle)
    (operation : HeapCalls.unary op value middle = some (.ok answer, finalHeap)) :
    EvaluatesIn (globals := globals) module env (.unaryOp op expression) heap (cost + 2) answer finalHeap := by
  intro anchors stack
  exact .next rfl ((evaluated anchors _).trans
    (.next (by simp [step, result, run, operation]) .refl))

theorem compare (left : EvaluatesIn (globals := globals) module env a heap ca av middle)
    (right : EvaluatesIn (globals := globals) module env b middle cb bv afterRight)
    (operation : HeapCalls.compare op av bv afterRight = some (.ok value, finalHeap)) :
    EvaluatesIn (globals := globals) module env (.compare a [(op, b)]) heap (ca + cb + 3) value finalHeap := by
  intro anchors stack
  have run := ReachesIn.next (step := step (globals := globals) module anchors) (state := ⟨.expr (.compare a [(op, b)]) env, stack, heap⟩) rfl
    ((left anchors _).trans (.next rfl ((right anchors _).trans
      (.next (following := ⟨.value value, stack, finalHeap⟩) (by simp [step, result, HeapCalls.run, operation]) .refl))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem conditional (condition : EvaluatesIn (globals := globals) module env test heap ct value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (branch : EvaluatesIn (globals := globals) module env (if flag then yes else no) middle cb answer finalHeap) :
    EvaluatesIn (globals := globals) module env (.ifExp test yes no) heap (ct + cb + 2) answer finalHeap := by
  intro anchors stack
  have run := ReachesIn.next (step := step (globals := globals) module anchors) (state := ⟨.expr (.ifExp test yes no) env, stack, heap⟩) rfl
    ((condition anchors _).trans (.next (by simp [step, HeapCalls.run, truth]) (branch anchors stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

inductive Arguments (module : Module) (env : Env) :
    List Expr → Heap → Nat → List Value → Heap → (globals : Mutable.Globals := []) → Prop where
  | nil {globals : Mutable.Globals} : Arguments (globals := globals) module env [] heap 0 [] heap
  | cons {globals : Mutable.Globals} :
      EvaluatesIn (globals := globals) module env expression heap headCost value middle →
      Arguments (globals := globals) module env expressions middle tailCost values finalHeap →
      Arguments (globals := globals) module env (expression :: expressions) heap
        (headCost + tailCost + 1) (value :: values) finalHeap

theorem arguments_reach (h : Arguments (globals := globals) module env expressions heap cost values finalHeap)
    (operation : Operation) (done : List Value) (anchors : Nat) (stack : List Frame) :
    ReachesIn (step (globals := globals) module anchors)
      (argumentsState operation env done expressions stack heap) cost
      ⟨.operation operation (done ++ values), stack, finalHeap⟩ := by
  induction h generalizing done with
  | nil => simp [argumentsState]; exact .refl
  | @cons expression heap headCost value middle expressions tailCost values finalHeap globals head tail ih =>
      have run := (head anchors (.arguments operation done expressions env :: stack)).trans
        (ReachesIn.next rfl (ih (done ++ [value])))
      simpa [argumentsState, List.append_assoc, Nat.add_assoc] using run

theorem call (arguments : Arguments (globals := globals) module env expressions heap ca values middle)
    (callee : ReturnsIn (globals := globals) module name values middle cc value finalHeap) :
    EvaluatesIn (globals := globals) module env (.call (.name name) expressions) heap (ca + cc + 1) value finalHeap :=
  fun anchors stack => .next rfl ((arguments_reach arguments (.call name) [] anchors stack).trans (callee anchors stack))

theorem tuple (arguments : Arguments (globals := globals) module env expressions heap cost values finalHeap)
    (nonempty : values ≠ []) :
    EvaluatesIn (globals := globals) module env (.tuple expressions) heap (cost + 2) (.ref finalHeap.length)
      (finalHeap ++ [.tuple values]) := by
  intro anchors stack
  exact .next rfl ((arguments_reach arguments .tuple [] anchors stack).trans
    (.next (by simp [step, result, run, primitive, Mutable.allocateTuple, nonempty, Except.map]) .refl))

theorem builtin (arguments : Arguments (globals := globals) module env expressions heap cost values middle)
    (operation : primitive (.builtin name) values middle = some (.ok value, finalHeap)) :
    EvaluatesIn (globals := globals) module env (.builtinCall name expressions) heap (cost + 2) value finalHeap := by
  intro anchors stack
  refine ReachesIn.next (following := argumentsState (.builtin name) env [] expressions stack heap) rfl ?_
  apply (arguments_reach arguments (.builtin name) [] anchors stack).trans
  cases name with
  | all | any => simp [primitive, Mutable.unsupported] at operation
  | _ => exact .next (by simp [step, result, run, operation]) .refl

theorem subscript {index : Expr} (ordinary : ∀ a b c, index ≠ .slice a b c)
    (receiver : EvaluatesIn (globals := globals) module env base heap cr value middle)
    (subscript : EvaluatesIn (globals := globals) module env index middle ci position afterIndex)
    (operation : Mutable.getItem value position afterIndex = some (.ok answer, finalHeap)) :
    EvaluatesIn (globals := globals) module env (.subscript base index) heap
      (cr + (ci + 2 + 1) + 1) answer finalHeap := by
  intro anchors stack
  have start : step (globals := globals) module anchors ⟨.expr (.subscript base index) env, stack, heap⟩ =
      .next ⟨.expr base env, .arguments .subscript [] [index] env :: stack, heap⟩ := by
    cases index <;> simp_all [step, argumentsState]
  exact .next start ((receiver anchors _).trans (.next rfl ((subscript anchors _).trans
    (.next rfl (.next (by simp [argumentsState, step, primitive, result, run, operation]) .refl)))))

def ComparesIn (module : Module) (env : Env) (left : Value) (op : CmpOp) (right : Expr)
    (rest : List (CmpOp × Expr)) (heap : Heap) (cost : Nat) (answer : Value) (finalHeap : Heap)
    (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, ReachesIn (step (globals := globals) module anchors)
    ⟨.expr right env, .chainRight op left rest env :: stack, heap⟩ cost
    ⟨.value answer, stack, finalHeap⟩

namespace ComparesIn

theorem last (evaluated : EvaluatesIn (globals := globals) module env right heap cost value middle)
    (operation : HeapCalls.compare op left value middle = some (.ok answer, finalHeap)) :
    ComparesIn (globals := globals) module env left op right [] heap (cost + 2) answer finalHeap := by
  intro anchors stack
  apply (evaluated anchors _).trans
  exact .next (following := ⟨.value answer, .chainResult value [] env :: stack, finalHeap⟩)
    (by simp [step, result, run, operation]) (.next rfl .refl)

theorem stop (evaluated : EvaluatesIn (globals := globals) module env right heap cost value middle)
    (operation : HeapCalls.compare op left value middle = some (.ok answer, finalHeap))
    (truth : Mutable.truth answer finalHeap = some (.ok false, finalHeap)) :
    ComparesIn (globals := globals) module env left op right (next :: rest) heap (cost + 2) answer finalHeap := by
  intro anchors stack
  apply (evaluated anchors _).trans
  exact .next (following := ⟨.value answer, .chainResult value (next :: rest) env :: stack, finalHeap⟩)
    (by simp [step, result, run, operation]) (.next (by simp [step, run, truth]) .refl)

theorem next (evaluated : EvaluatesIn (globals := globals) module env right heap ca value middle)
    (operation : HeapCalls.compare op left value middle = some (.ok compared, afterComparison))
    (truth : Mutable.truth compared afterComparison = some (.ok true, afterComparison))
    (following : ComparesIn (globals := globals) module env value nextOp nextRight rest afterComparison cb answer finalHeap) :
    ComparesIn (globals := globals) module env left op right ((nextOp, nextRight) :: rest) heap
      (ca + (cb + 2)) answer finalHeap := by
  intro anchors stack
  apply (evaluated anchors _).trans
  exact .next (following := ⟨.value compared, .chainResult value ((nextOp, nextRight) :: rest) env :: stack, afterComparison⟩)
    (by simp [step, result, run, operation])
    (.next (by simp [step, run, truth]) (following anchors stack))

end ComparesIn

theorem chain (left : EvaluatesIn (globals := globals) module env expression heap ca value middle)
    (following : ComparesIn (globals := globals) module env value op right (next :: rest) middle cb answer finalHeap) :
    EvaluatesIn (globals := globals) module env (.compare expression ((op, right) :: next :: rest)) heap
      (ca + (cb + 1) + 1) answer finalHeap :=
  fun anchors stack => .next rfl ((left anchors _).trans (.next rfl (following anchors stack)))

theorem boolean_stop (evaluated : EvaluatesIn (globals := globals) module env first heap cost value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (stop : (match op with | .and => !flag | .or => flag) = true) :
    EvaluatesIn (globals := globals) module env (.boolOp op (first :: rest)) heap (cost + 2) value middle :=
  fun anchors stack => .next rfl ((evaluated anchors _).trans
    (.next (by cases op <;> cases flag <;> simp_all only [Bool.not_true, Bool.not_false, Bool.false_eq_true]; all_goals simp [step, run, truth]) .refl))

theorem boolean_last (evaluated : EvaluatesIn (globals := globals) module env expression heap cost value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle)) :
    EvaluatesIn (globals := globals) module env (.boolOp op [expression]) heap (cost + 2) value middle := by
  intro anchors stack
  refine .next rfl ((evaluated anchors _).trans (.next ?_ .refl))
  cases op <;> cases flag <;> simp [step, run, truth]

/-- The next Boolean operand reuses the frame: it saves the initial transition
of the recursive Boolean expression. -/
theorem boolean_next (evaluated : EvaluatesIn (globals := globals) module env first heap ca value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (continues : (match op with | .and => !flag | .or => flag) = false)
    (rest : EvaluatesIn (globals := globals) module env (.boolOp op (next :: tail)) middle (cb + 1) answer finalHeap) :
    EvaluatesIn (globals := globals) module env (.boolOp op (first :: next :: tail)) heap
      (ca + (cb + 1) + 1) answer finalHeap := by
  intro anchors stack
  refine .next rfl ((evaluated anchors _).trans ?_)
  cases rest anchors stack with
  | next transition following =>
      simp only [step, protectGenerator_next, Step.next.injEq] at transition
      subst transition
      exact .next (by cases op <;> cases flag <;> simp_all only [Bool.not_true, Bool.not_false, Bool.true_eq_false]; all_goals simp [step, run, truth]) following

theorem add (receiver : EvaluatesIn (globals := globals) module env base heap cr (.ref address) middle)
    (found : middle[address]? = some (.set old))
    (item : EvaluatesIn (globals := globals) module env expression middle ci (.scalar value) afterItem)
    (items : afterItem[address]? = some (.set current)) :
    EvaluatesIn (globals := globals) module env (.call (.attribute base "add") [expression]) heap
      (cr + (ci + 3) + 1) (.scalar .none) (afterItem.set address (.set (ScalarSet.insert current value))) := by
  intro anchors stack
  refine .next rfl ((receiver anchors _).trans ?_)
  refine .next (following := ⟨.expr expression env, .arguments (.add address) [] [] env :: stack, middle⟩)
    (by simp [step, run, Mutable.addReceiver, found, argumentsState]) ?_
  exact (item anchors _).trans (.next (following := ⟨.operation (.add address) [.scalar value], stack, afterItem⟩) rfl
    (.next (by simp [step, result, run, primitive, Mutable.addItem, items, Except.map]) .refl))

end EvaluatesIn

private def rangeState (name : String) (env : Env) (done : List Value)
    (expressions : List Expr) (body otherwise following : List Stmt)
    (stack : List Frame) (heap : Heap) : State :=
  match expressions with
  | [] => ⟨.startRange name done body otherwise following env, stack, heap⟩
  | first :: rest =>
      ⟨.expr first env, .rangeArguments name done rest body otherwise following env :: stack, heap⟩

private theorem range_reach
    (h : EvaluatesIn.Arguments (globals := globals) module env expressions heap cost values finalHeap)
    (done : List Value) (anchors : Nat) (stack : List Frame) :
    ReachesIn (step (globals := globals) module anchors)
      (rangeState name env done expressions body otherwise following stack heap) cost
      ⟨.startRange name (done ++ values) body otherwise following env, stack, finalHeap⟩ := by
  induction h generalizing done with
  | nil => simp [rangeState]; exact .refl
  | @cons expression heap headCost value middle expressions tailCost values finalHeap globals head tail ih =>
      have run := (head anchors (.rangeArguments name done expressions body otherwise following env :: stack)).trans
        (ReachesIn.next rfl (ih (done ++ [value])))
      simpa [rangeState, List.append_assoc, Nat.add_assoc] using run

namespace BlockContinuesIn

theorem for_range (arguments : EvaluatesIn.Arguments (globals := globals) module env expressions heap ca values middle)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (executed : BlockContinuesIn (globals := globals) module env [.rangeStepLoop name start stop stride body otherwise]
      middle cb finalEnv finalHeap) :
    BlockContinuesIn (globals := globals) module env [.forIn (.name name) (.call (.name "range") expressions) body otherwise]
      heap (ca + (cb + 1) + 1) finalEnv finalHeap := by
  intro following anchors stack
  exact .next rfl ((range_reach arguments [] anchors stack).trans
    (.next (by simp [step, bounds]) (executed following anchors stack)))

theorem augAssign (lookup : env name = some left)
    (evaluated : EvaluatesIn (globals := globals) module env expression heap cost right middle)
    (operation : inplace op left right middle = some (.ok value, finalHeap)) :
    BlockContinuesIn (globals := globals) module env [.augAssign (.name name) op expression] heap
      (1 + (cost + 2 + 1) + 1) (setLocal env name value) finalHeap := by
  intro following anchors stack
  refine .next rfl ((EvaluatesIn.lookup (globals := globals) (module := module) (heap := heap) lookup anchors _).trans (.next rfl ?_))
  exact (evaluated anchors _).trans (.next
    (following := ⟨.value value, .assign name following env :: stack, finalHeap⟩)
    (by simp [step, result, run, operation]) (.next rfl .refl))

theorem nil : BlockContinuesIn (globals := globals) module env [] heap 0 env heap := fun _ _ _ => .refl

theorem append (first : BlockContinuesIn (globals := globals) module env body heap ca middleEnv middleHeap)
    (second : BlockContinuesIn (globals := globals) module middleEnv rest middleHeap cb finalEnv finalHeap) :
    BlockContinuesIn (globals := globals) module env (body ++ rest) heap (ca + cb) finalEnv finalHeap := by
  intro following anchors stack
  simpa only [List.append_assoc] using
    (first (rest ++ following) anchors stack).trans (second following anchors stack)

theorem assign (evaluated : EvaluatesIn (globals := globals) module env expression heap cost value finalHeap) :
    BlockContinuesIn (globals := globals) module env [.assign [.name name] expression] heap
      (cost + 2) (setLocal env name value) finalHeap :=
  fun _ anchors _ => .next rfl ((evaluated anchors _).trans (.next rfl .refl))

theorem unpack (targets : Calls.targetNames expressions = some names)
    (evaluated : EvaluatesIn (globals := globals) module env expression heap cost value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, finalHeap))
    (arity : names.length = items.length) :
    BlockContinuesIn (globals := globals) module env [.assign [.tuple expressions] expression] heap
      (cost + 2) (assignNames env names items) finalHeap := by
  intro following anchors stack
  exact .next (following := ⟨.expr expression env, .unpack names following env :: stack, heap⟩)
    (by simp [step, targets]) ((evaluated anchors _).trans
    (.next (by simp [step, run, sequence, arity]) .refl))

theorem discard (evaluated : EvaluatesIn (globals := globals) module env expression heap cost value finalHeap) :
    BlockContinuesIn (globals := globals) module env [.expr expression] heap (cost + 2) env finalHeap :=
  fun _ anchors _ => .next rfl ((evaluated anchors _).trans (.next rfl .refl))

theorem branch (evaluated : EvaluatesIn (globals := globals) module env condition heap cc value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (body : BlockContinuesIn (globals := globals) module env (if flag then yes else no) middle cb finalEnv finalHeap) :
    BlockContinuesIn (globals := globals) module env [.ifThen condition yes no] heap (cc + cb + 2) finalEnv finalHeap := by
  intro following anchors stack
  have run := ReachesIn.next (step := step (globals := globals) module anchors) (state := ⟨.block ([.ifThen condition yes no] ++ following) env, stack, heap⟩) rfl
    ((evaluated anchors _).trans (.next (by simp [step, HeapCalls.run, truth]) (body following anchors stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem while_loop (evaluated : EvaluatesIn (globals := globals) module env condition heap cc value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockContinuesIn (globals := globals) module env
      (if flag then body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)] else otherwise)
      middle cb finalEnv finalHeap) :
    BlockContinuesIn (globals := globals) module env [.whileDo condition body otherwise] heap (cc + cb + 2) finalEnv finalHeap := by
  intro following anchors stack
  have run := ReachesIn.next (step := step (globals := globals) module anchors) (state := ⟨.block ([.whileDo condition body otherwise] ++ following) env, stack, heap⟩) rfl
    ((evaluated anchors _).trans (.next (by simp [step, HeapCalls.run, truth]) (rest following anchors stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem range_step (continues : Calls.rangeContinues next stop stride = true)
    (rest : BlockContinuesIn (globals := globals) module (setLocal env name (.scalar (.int next)))
      (body ++ [Calls.loopContinuation body (.rangeStepLoop name (next + stride) stop stride body otherwise)])
      heap cost finalEnv finalHeap) :
    BlockContinuesIn (globals := globals) module env [.rangeStepLoop name next stop stride body otherwise]
      heap (cost + 1) finalEnv finalHeap := by
  intro following anchors stack
  refine .next ?_ (rest following anchors stack)
  simp [step, continues, List.append_assoc]

theorem range_done (finished : Calls.rangeContinues next stop stride = false)
    (rest : BlockContinuesIn (globals := globals) module env otherwise heap cost finalEnv finalHeap) :
    BlockContinuesIn (globals := globals) module env [.rangeStepLoop name next stop stride body otherwise]
      heap (cost + 1) finalEnv finalHeap :=
  fun following anchors stack => .next (by simp [step, finished]) (rest following anchors stack)

theorem loop_resume (rest : BlockContinuesIn (globals := globals) module env [next] heap cost finalEnv finalHeap) :
    BlockContinuesIn (globals := globals) module env [.loopResume next] heap (cost + 1) finalEnv finalHeap :=
  fun following anchors stack => .next rfl (rest following anchors stack)

theorem returns (first : BlockContinuesIn (globals := globals) module env body heap ca middleEnv middleHeap)
    (rest : BlockReturnsIn (globals := globals) module middleEnv following middleHeap cb answer finalHeap) :
    BlockReturnsIn (globals := globals) module env (body ++ following) heap (ca + cb) answer finalHeap :=
  fun anchors stack => (first following anchors stack).trans (rest anchors stack)

end BlockContinuesIn

namespace BlockReturnsIn

theorem branch (evaluated : EvaluatesIn (globals := globals) module env condition heap cc value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockReturnsIn (globals := globals) module env ((if flag then yes else no) ++ body)
      middle cb answer finalHeap) :
    BlockReturnsIn (globals := globals) module env (.ifThen condition yes no :: body) heap
      (cc + (cb + 1) + 1) answer finalHeap :=
  fun anchors stack => .next rfl ((evaluated anchors _).trans
    (.next (by simp [step, run, truth]) (rest anchors stack)))

theorem while_loop (evaluated : EvaluatesIn (globals := globals) module env condition heap cc value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockReturnsIn (globals := globals) module env
      ((if flag then body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)] else otherwise) ++ following)
      middle cb answer finalHeap) :
    BlockReturnsIn (globals := globals) module env (.whileDo condition body otherwise :: following) heap
      (cc + (cb + 1) + 1) answer finalHeap :=
  fun anchors stack => .next rfl ((evaluated anchors _).trans
    (.next (by simp [step, run, truth]) (rest anchors stack)))

theorem loop_resume (rest : BlockReturnsIn (globals := globals) module env (next :: following) heap cost answer finalHeap) :
    BlockReturnsIn (globals := globals) module env (.loopResume next :: following) heap (cost + 1) answer finalHeap :=
  fun anchors stack => .next rfl (rest anchors stack)

theorem break_loop (target : Calls.loopTarget body = some (next, following))
    (rest : BlockReturnsIn (globals := globals) module env following heap cost answer finalHeap) :
    BlockReturnsIn (globals := globals) module env (.breakLoop :: body) heap (cost + 1) answer finalHeap :=
  fun anchors stack => .next (by simp [step, target]) (rest anchors stack)

theorem continue_loop (target : Calls.loopTarget body = some (next, following))
    (rest : BlockReturnsIn (globals := globals) module env (next :: following) heap cost answer finalHeap) :
    BlockReturnsIn (globals := globals) module env (.continueLoop :: body) heap (cost + 1) answer finalHeap :=
  fun anchors stack => .next (by simp [step, target]) (rest anchors stack)

theorem for_range (arguments : EvaluatesIn.Arguments (globals := globals) module env expressions heap ca values middle)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (rest : BlockReturnsIn (globals := globals) module env (.rangeStepLoop name start stop stride body otherwise :: following)
      middle cb answer finalHeap) :
    BlockReturnsIn (globals := globals) module env (.forIn (.name name) (.call (.name "range") expressions) body otherwise :: following)
      heap (ca + (cb + 1) + 1) answer finalHeap := by
  intro anchors stack
  exact .next rfl ((range_reach arguments [] anchors stack).trans
    (.next (by simp [step, bounds]) (rest anchors stack)))

theorem return_value (evaluated : EvaluatesIn (globals := globals) module env expression heap cost value finalHeap) :
    BlockReturnsIn (globals := globals) module env (.return expression :: following) heap (cost + 1) value finalHeap :=
  fun anchors stack => .next rfl (evaluated anchors stack)

theorem assign (evaluated : EvaluatesIn (globals := globals) module env expression heap ca value middle)
    (rest : BlockReturnsIn (globals := globals) module (setLocal env name value) following middle cb answer finalHeap) :
    BlockReturnsIn (globals := globals) module env (.assign [.name name] expression :: following) heap
      (ca + cb + 2) answer finalHeap := by
  intro anchors stack
  have run := ReachesIn.next (step := step (globals := globals) module anchors) (state := ⟨.block (.assign [.name name] expression :: following) env, stack, heap⟩)
    rfl ((evaluated anchors _).trans (.next rfl (rest anchors stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem function (found : findFunctionIn module.body name = some (args, body))
    (arity : completeArguments args values = some completed)
    (evaluated : BlockReturnsIn (globals := globals) module (functionEnv args body completed globals) (executableBody body) heap cost value finalHeap) :
    ReturnsIn (globals := globals) module name values heap (cost + 1) value finalHeap :=
  fun anchors stack => .next (by simp [step, found, arity]) (evaluated anchors stack)

end BlockReturnsIn

end Cost
end FormalSW.PyAst.HeapCalls
