import lang.py.FormalSW.Runtime

/-! Scalar Python execution with an explicit expression and function call stack.
Recursive calls consume transitions, not Lean recursion fuel. Unsupported syntax
remains unsupported, and exceptions propagate out of callers. -/

namespace FormalSW.PyAst.Calls

inductive Frame where
  | binaryLeft (op : BinOp) (right : Expr) (env : ScalarEnv)
  | binaryRight (op : BinOp) (left : Constant)
  | compareLeft (op : CmpOp) (right : Expr) (env : ScalarEnv)
  | compareRight (op : CmpOp) (left : Constant)
  | unary (op : UnaryOp)
  | boolean (op : BoolOp) (rest : List Expr) (env : ScalarEnv)
  | conditional (yes no : Expr) (env : ScalarEnv)
  | arguments (name : String) (done : List Constant) (rest : List Expr) (env : ScalarEnv)
  | assign (name : String) (rest : List Stmt) (env : ScalarEnv)
  | branch (yes no rest : List Stmt) (env : ScalarEnv)
  | discard (rest : List Stmt) (env : ScalarEnv)

inductive Work where
  | expr (expression : Expr) (env : ScalarEnv)
  | block (body : List Stmt) (env : ScalarEnv)
  | value (value : Constant)
  | invoke (name : String) (values : List Constant)

structure State where
  work : Work
  stack : List Frame

def outcome (result : Option (Except ExceptionObject Constant)) (stack : List Frame) :
    Step State Constant :=
  match result with
  | some (.ok value) => .next ⟨.value value, stack⟩
  | some (.error exception) => .done (.error exception)
  | none => .unsupported

def step (module : Module) (state : State) : Step State Constant :=
  let ⟨work, stack⟩ := state
  match work with
  | .invoke name values =>
      match findFunctionIn module.body name with
      | some (args, body) =>
          if args.length = values.length then
            .next ⟨.block (executableBody body) (argumentEnv args values), stack⟩
          else .unsupported
      | none => .unsupported
  | .expr expression env =>
      match expression with
      | .constant value => .next ⟨.value value, stack⟩
      | .name name => outcome (Except.ok <$> env name) stack
      | .binOp left op right =>
          .next ⟨.expr left env, .binaryLeft op right env :: stack⟩
      | .unaryOp op expr => .next ⟨.expr expr env, .unary op :: stack⟩
      | .compare left [(op, right)] =>
          .next ⟨.expr left env, .compareLeft op right env :: stack⟩
      | .boolOp _ [] => .unsupported
      | .boolOp op (first :: rest) =>
          .next ⟨.expr first env, .boolean op rest env :: stack⟩
      | .ifExp test yes no => .next ⟨.expr test env, .conditional yes no env :: stack⟩
      | .call (.name name) [] => .next ⟨.invoke name [], stack⟩
      | .call (.name name) (first :: rest) =>
          .next ⟨.expr first env, .arguments name [] rest env :: stack⟩
      | _ => .unsupported
  | .block body env =>
      match body with
      | [] => .next ⟨.value .none, stack⟩
      | .return expr :: _ => .next ⟨.expr expr env, stack⟩
      | .assign [.name name] expr :: rest =>
          .next ⟨.expr expr env, .assign name rest env :: stack⟩
      | .augAssign (.name name) op expr :: rest =>
          .next ⟨.expr (.binOp (.name name) op expr) env, .assign name rest env :: stack⟩
      | .ifThen condition yes no :: rest =>
          .next ⟨.expr condition env, .branch yes no rest env :: stack⟩
      | .whileDo condition body otherwise :: rest =>
          .next ⟨.expr condition env,
            .branch (body ++ [.whileDo condition body otherwise]) otherwise rest env :: stack⟩
      | .expr expr :: rest => .next ⟨.expr expr env, .discard rest env :: stack⟩
      | _ => .unsupported
  | .value value =>
      match stack with
      | [] => .done (.ok value)
      | frame :: stack =>
          match frame with
          | .binaryLeft op right env => .next ⟨.expr right env, .binaryRight op value :: stack⟩
          | .binaryRight op left => outcome (scalarBinary op left value) stack
          | .compareLeft op right env => .next ⟨.expr right env, .compareRight op value :: stack⟩
          | .compareRight op left =>
              outcome ((fun b => .ok (.bool b)) <$> scalarCompare op left value) stack
          | .unary op => outcome (scalarExpr (fun _ => none) (.unaryOp op (.constant value))) stack
          | .boolean op rest env =>
              if (match op with | .and => !scalarTruth value | .or => scalarTruth value) then
                .next ⟨.value value, stack⟩
              else match rest with
                | [] => .next ⟨.value value, stack⟩
                | first :: rest => .next ⟨.expr first env, .boolean op rest env :: stack⟩
          | .conditional yes no env =>
              .next ⟨.expr (if scalarTruth value then yes else no) env, stack⟩
          | .arguments name done rest env =>
              match rest with
              | [] => .next ⟨.invoke name (done ++ [value]), stack⟩
              | first :: rest =>
                  .next ⟨.expr first env, .arguments name (done ++ [value]) rest env :: stack⟩
          | .assign name rest env => .next ⟨.block rest (env.set name value), stack⟩
          | .branch yes no rest env =>
              .next ⟨.block ((if scalarTruth value then yes else no) ++ rest) env, stack⟩
          | .discard rest env => .next ⟨.block rest env, stack⟩

def function (module : Module) (name : String) (args : List Constant) : Execution Constant :=
  ⟨State, ⟨.invoke name args, []⟩, step module⟩

/-- A finite sequence of transitions, ending before the continuation executes. -/
inductive Reaches (module : Module) : State → State → Prop where
  | refl : Reaches module state state
  | next : step module state = .next following →
      Reaches module following final → Reaches module state final

theorem Reaches.trans (h : Reaches module a b) (rest : Reaches module b c) :
    Reaches module a c := by
  induction h with
  | refl => exact rest
  | next h _ ih => exact .next h (ih rest)

theorem Reaches.finishes (h : Reaches module a b)
    (rest : Finishes (step module) b result) : Finishes (step module) a result := by
  induction h with
  | refl => exact rest
  | next h _ ih => exact .next h (ih rest)

/-- Expression evaluation is compositional in every caller continuation. -/
def Evaluates (module : Module) (env : ScalarEnv) (expression : Expr) (value : Constant) : Prop :=
  ∀ stack, Reaches module ⟨.expr expression env, stack⟩ ⟨.value value, stack⟩

def ReturnsValue (module : Module) (name : String) (args : List Constant) (value : Constant) : Prop :=
  ∀ stack, Reaches module ⟨.invoke name args, stack⟩ ⟨.value value, stack⟩

theorem ReturnsValue.finishes (h : ReturnsValue module name args value) :
    Finishes (function module name args).step (function module name args).initial (.ok value) :=
  (h []).finishes (.done rfl)

theorem ReturnsValue.returns (h : ReturnsValue module name args value) :
    (function module name args).Returns := ⟨value, h.finishes⟩

theorem ReturnsValue.equiv (left : ReturnsValue m f args value)
    (right : ReturnsValue m' g args' value) :
    (function m f args).Equiv (function m' g args') := by
  intro result
  constructor
  · intro h
    have eq := h.unique left.finishes
    rw [eq]
    exact right.finishes
  · intro h
    have eq := h.unique right.finishes
    rw [eq]
    exact left.finishes

namespace Evaluates

theorem constant : Evaluates module env (.constant value) value := fun _ => .next rfl .refl

theorem lookup (h : env name = some value) : Evaluates module env (.name name) value := by
  intro stack
  exact .next (by simp [step, outcome, h]) .refl

theorem binary (left : Evaluates module env a av) (right : Evaluates module env b bv)
    (result : scalarBinary op av bv = some (.ok value)) :
    Evaluates module env (.binOp a op b) value := by
  intro stack
  exact .next rfl ((left _).trans (.next rfl
    ((right _).trans (.next (by simp [step, outcome, result]) .refl))))

theorem compare (left : Evaluates module env a av) (right : Evaluates module env b bv)
    (result : scalarCompare op av bv = some value) :
    Evaluates module env (.compare a [(op, b)]) (.bool value) := by
  intro stack
  exact .next rfl ((left _).trans (.next rfl
    ((right _).trans (.next (by simp [step, outcome, result]) .refl))))

theorem conditional (condition : Evaluates module env test c)
    (branch : Evaluates module env (if scalarTruth c then yes else no) value) :
    Evaluates module env (.ifExp test yes no) value := by
  intro stack
  exact .next rfl ((condition _).trans (.next rfl (branch _)))

theorem boolean_last (h : Evaluates module env expression value) :
    Evaluates module env (.boolOp op [expression]) value := by
  intro stack
  refine .next rfl ((h _).trans (.next ?_ .refl))
  cases op <;> simp [step]

theorem boolean_stop (h : Evaluates module env expression value)
    (stop : (match op with | .and => !scalarTruth value | .or => scalarTruth value) = true) :
    Evaluates module env (.boolOp op (expression :: rest)) value := by
  intro stack
  exact .next rfl ((h _).trans (.next (by simp [step, stop]) .refl))

theorem boolean_continue (h : Evaluates module env expression first)
    (proceed : (match op with | .and => !scalarTruth first | .or => scalarTruth first) = false)
    (rest : Evaluates module env (.boolOp op (next :: tail)) value) :
    Evaluates module env (.boolOp op (expression :: next :: tail)) value := by
  intro stack
  have remaining := rest stack
  cases remaining with
  | next stepEq remaining =>
      simp only [step, Step.next.injEq] at stepEq
      subst stepEq
      exact .next rfl ((h _).trans (.next (by simp [step, proceed]) remaining))

private def argumentsWork (name : String) (env : ScalarEnv) (done : List Constant)
    (expressions : List Expr) (stack : List Frame) : State :=
  match expressions with
  | [] => ⟨.invoke name done, stack⟩
  | first :: rest => ⟨.expr first env, .arguments name done rest env :: stack⟩

inductive Arguments (module : Module) (env : ScalarEnv) : List Expr → List Constant → Prop where
  | nil : Arguments module env [] []
  | cons : Evaluates module env expression value → Arguments module env expressions values →
      Arguments module env (expression :: expressions) (value :: values)

private theorem arguments_reach
    (h : Arguments module env expressions values) (done : List Constant)
    (stack : List Frame) :
    Reaches module (argumentsWork name env done expressions stack)
      ⟨.invoke name (done ++ values), stack⟩ := by
  induction h generalizing done with
  | nil => simp [argumentsWork]; exact .refl
  | @cons expression value expressions values head tail ih =>
      apply (head _).trans
      refine .next (following := argumentsWork name env (done ++ [value]) expressions stack) ?_ ?_
      · cases expressions <;> rfl
      · simpa [List.append_assoc] using ih (done ++ [value])

theorem call (arguments : Arguments module env expressions values)
    (result : ReturnsValue module name values value) :
    Evaluates module env (.call (.name name) expressions) value := by
  intro stack
  refine .next (following := argumentsWork name env [] expressions stack) ?_ ?_
  · cases expressions <;> rfl
  · exact (arguments_reach arguments [] stack).trans (result stack)

end Evaluates

def BlockReturns (module : Module) (env : ScalarEnv) (body : List Stmt) (value : Constant) : Prop :=
  ∀ stack, Reaches module ⟨.block body env, stack⟩ ⟨.value value, stack⟩

namespace BlockReturns

theorem return_value (h : Evaluates module env expression value) :
    BlockReturns module env (.return expression :: rest) value :=
  fun stack => .next rfl (h stack)

theorem assign (h : Evaluates module env expression value)
    (rest : BlockReturns module (env.set name value) body result) :
    BlockReturns module env (.assign [.name name] expression :: body) result := by
  intro stack
  exact .next rfl ((h _).trans (.next rfl (rest stack)))

theorem branch (h : Evaluates module env condition value)
    (rest : BlockReturns module env ((if scalarTruth value then yes else no) ++ body) result) :
    BlockReturns module env (.ifThen condition yes no :: body) result := by
  intro stack
  exact .next rfl ((h _).trans (.next rfl (rest stack)))

theorem function (found : findFunctionIn module.body name = some (args, body))
    (arity : args.length = values.length)
    (h : BlockReturns module (argumentEnv args values) (executableBody body) value) :
    ReturnsValue module name values value := by
  intro stack
  exact .next (by simp [step, found, arity]) (h stack)

end BlockReturns

end FormalSW.PyAst.Calls
