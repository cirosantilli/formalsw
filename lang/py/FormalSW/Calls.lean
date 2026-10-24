import lang.py.FormalSW.Math
import lang.py.FormalSW.Strings

/-! Scalar Python execution with an explicit expression and function call stack.
Recursive calls consume transitions, not Lean recursion fuel. Unsupported syntax
remains unsupported, and exceptions propagate out of callers. -/

namespace FormalSW.PyAst.Calls

/-- Operations whose bindings have already been resolved by source checking. -/
inductive Primitive where
  | builtin (function : Builtin)
  | raiseException (typeName : String)
  | subscript
  | slice

/-- Python's positional maximum keeps the first value on ties, preserving its
type (in particular, `True` and `1` compare equal but are distinct results). -/
def maximumFrom (best : Constant) : List Constant → Except ExceptionObject Constant
  | [] => .ok best
  | value :: rest => match scalarCompare .gt value best with
      | some larger => maximumFrom (if larger then value else best) rest
      | none => .error { typeName := "TypeError", args := [] }

def positionalMaximum : List Constant → Option (Except ExceptionObject Constant)
  | first :: second :: rest => some (maximumFrom first (second :: rest))
  | _ => none

/-- Python's positional minimum also keeps the first value on ties. -/
def minimumFrom (best : Constant) : List Constant → Except ExceptionObject Constant
  | [] => .ok best
  | value :: rest => match scalarCompare .lt value best with
      | some smaller => minimumFrom (if smaller then value else best) rest
      | none => .error { typeName := "TypeError", args := [] }

def positionalMinimum : List Constant → Option (Except ExceptionObject Constant)
  | first :: second :: rest => some (minimumFrom first (second :: rest))
  | _ => none

/-- Parsing failures use the same exception-class abstraction as other implicit errors. -/
def parsedInteger : Py.Builtin.Result Int → Option (Except ExceptionObject Constant)
  | .ok value => some (.ok (.int value))
  | .error (.valueError _) => some (.error { typeName := "ValueError", args := [] })
  | .error _ => none

/-- Integer conversion includes unbounded decimal text and byte parsing. -/
def integerConversion : List Constant → Option (Except ExceptionObject Constant)
  | [] => some (.ok (.int 0))
  | [.int value] => some (.ok (.int value))
  | [.bool value] => some (.ok (.int (if value then 1 else 0)))
  | [.none] => some (.error { typeName := "TypeError", args := [] })
  | [.string text] => parsedInteger (Py.Builtin.Int.parseText text)
  | [.bytes bytes] => parsedInteger (Py.Builtin.Int.parseDecimal (bytes.map UInt8.toNat))
  | _ => none

/-- Length counts Unicode characters in text and octets in bytes. -/
def length : Constant → Except ExceptionObject Constant
  | .string text => .ok (.int text.length)
  | .bytes bytes => .ok (.int bytes.length)
  | _ => .error { typeName := "TypeError", args := [] }

def Primitive.apply : Primitive → List Constant → Option (Except ExceptionObject Constant)
  | .raiseException typeName, args => some (.error { typeName, args })
  | .builtin .len, [value] => some (length value)
  | .builtin .int, values => integerConversion values
  | .builtin .str, values => some (Strings.str values)
  | .builtin .max, values => positionalMaximum values
  | .builtin .min, values => positionalMinimum values
  | .builtin .intBitLength, [value] => some (Math.bitLengthCall value)
  | .subscript, [value, index] => some (Strings.get value index)
  | .slice, [value, lower, upper, stride] => some (Strings.slice value lower upper stride)
  | _, _ => none

/-- A generator's private environment is kept apart from its caller's locals. -/
structure RangeSum where
  name : String
  element : Expr
  conditions : List Expr
  stop : Int
  stride : Int
  env : ScalarEnv

def RangeSum.filter (sum : RangeSum) : Expr :=
  if sum.conditions.isEmpty then .constant (.bool true) else .boolOp .and sum.conditions

/-- Range extrema retain the winning element and its already evaluated key. -/
structure RangeExtremum where
  maximum : Bool
  key : String
  stop : Int
  stride : Int

/-- Strict comparison preserves the first element on equal keys. -/
def RangeExtremum.choose (range : RangeExtremum) (next : Int) (score : Constant)
    (best : Option (Int × Constant)) : Except ExceptionObject (Int × Constant) :=
  match best with
  | none => .ok (next, score)
  | some (winner, previous) =>
      match scalarCompare (if range.maximum then .gt else .lt) score previous with
      | some better => .ok (if better then (next, score) else (winner, previous))
      | none => .error { typeName := "TypeError", args := [] }

inductive Frame where
  | binaryLeft (op : BinOp) (right : Expr) (env : ScalarEnv)
  | binaryRight (op : BinOp) (left : Constant)
  | compareLeft (op : CmpOp) (right : Expr) (env : ScalarEnv)
  | compareRight (op : CmpOp) (left : Constant)
  | chainLeft (op : CmpOp) (right : Expr) (rest : List (CmpOp × Expr)) (env : ScalarEnv)
  | chainRight (op : CmpOp) (left : Constant) (rest : List (CmpOp × Expr)) (env : ScalarEnv)
  | unary (op : UnaryOp)
  | boolean (op : BoolOp) (rest : List Expr) (env : ScalarEnv)
  | conditional (yes no : Expr) (env : ScalarEnv)
  | arguments (name : String) (done : List Constant) (rest : List Expr) (env : ScalarEnv)
  | primitiveArguments (operation : Primitive) (done : List Constant) (rest : List Expr) (env : ScalarEnv)
  | assign (name : String) (rest : List Stmt) (env : ScalarEnv)
  | branch (yes no rest : List Stmt) (env : ScalarEnv)
  | discard (rest : List Stmt) (env : ScalarEnv)
  | assertion (message : Option Expr) (rest : List Stmt) (env : ScalarEnv)
  | assertionMessage
  | unpack (names : List String) (done : List Constant) (rest : List Expr)
      (body : List Stmt) (env : ScalarEnv)
  | rangeArguments (name : String) (done : List Constant) (rest : List Expr)
      (body otherwise following : List Stmt) (env : ScalarEnv)

  | sumArguments (name : String) (element : Expr) (conditions : List Expr)
      (done : List Constant) (rest : List Expr) (env : ScalarEnv)
  | sumFilter (sum : RangeSum) (next total : Int)
  | sumElement (sum : RangeSum) (next total : Int)
  | extremumArguments (maximum : Bool) (key : String)
      (done : List Constant) (rest : List Expr) (env : ScalarEnv)
  | extremumKey (range : RangeExtremum) (next : Int) (best : Option (Int × Constant))

inductive Work where
  | expr (expression : Expr) (env : ScalarEnv)
  | block (body : List Stmt) (env : ScalarEnv)
  | value (value : Constant)
  | invoke (name : String) (values : List Constant)
  | primitive (operation : Primitive) (values : List Constant)
  | startRange (name : String) (values : List Constant)
      (body otherwise following : List Stmt) (env : ScalarEnv)

  | startSum (name : String) (element : Expr) (conditions : List Expr)
      (values : List Constant) (env : ScalarEnv)
  | sumLoop (sum : RangeSum) (next total : Int)
  | startExtremum (maximum : Bool) (key : String) (values : List Constant)
  | extremumLoop (range : RangeExtremum) (next : Int) (best : Option (Int × Constant))

structure State where
  work : Work
  stack : List Frame

/-- Fill missing trailing arguments from definition-time scalar defaults. The
source checker excludes effectful or mutable defaults and keyword arguments. -/
def completeArguments : List Arg → List Constant → Option (List Constant)
  | [], [] => some []
  | [], _ :: _ => none
  | arg :: args, [] => do
      let value ← arg.defaultValue
      return value :: (← completeArguments args [])
  | _ :: args, value :: values => do
      return value :: (← completeArguments args values)

def outcome (result : Option (Except ExceptionObject Constant)) (stack : List Frame) :
    Step State Constant :=
  match result with
  | some (.ok value) => .next ⟨.value value, stack⟩
  | some (.error exception) => .done (.error exception)
  | none => .unsupported

private def primitiveState (operation : Primitive) (env : ScalarEnv) (done : List Constant)
    (expressions : List Expr) (stack : List Frame) : State :=
  match expressions with
  | [] => ⟨.primitive operation done, stack⟩
  | first :: rest => ⟨.expr first env, .primitiveArguments operation done rest env :: stack⟩

def targetNames (targets : List Expr) : Option (List String) :=
  targets.mapM fun target => match target with
    | .name name => some name
    | _ => none

/-- Bind after all right-hand sides have been evaluated in the old environment. -/
def assignNames (env : ScalarEnv) (names : List String) : List Constant → ScalarEnv
  | [] => env
  | value :: values => match names with
    | [] => env
    | name :: names => assignNames (env.set name value) names values

/-- Builtin range accepts integer indices, including booleans. Implicit error
messages use the same abstraction as the other scalar builtins. -/
def rangeBounds (values : List Constant) : Except ExceptionObject (Int × Int × Int) := do
  let numbers ← values.mapM fun value => match value with
    | .int n => .ok n
    | .bool b => .ok (if b then 1 else 0)
    | _ => .error { typeName := "TypeError", args := [] }
  let (start, stop, stride) ← match numbers with
    | [stop] => .ok (0, stop, 1)
    | [start, stop] => .ok (start, stop, 1)
    | [start, stop, stride] => .ok (start, stop, stride)
    | _ => .error { typeName := "TypeError", args := [] }
  if stride = 0 then .error { typeName := "ValueError", args := [] }
  else .ok (start, stop, stride)

def rangeContinues (next stop stride : Int) : Bool :=
  decide (0 < stride ∧ next < stop ∨ stride < 0 ∧ stop < next)

mutual
  /-- A transfer in a nested loop body belongs to that loop. A transfer in its
  `else` block belongs to the surrounding loop instead. -/
  def loopControlStmt : Stmt → Bool
    | .breakLoop | .continueLoop => true
    | .ifThen _ yes no => loopControl yes || loopControl no
    | .whileDo _ _ otherwise | .forIn _ _ _ otherwise | .forZip _ _ _ otherwise
      | .forReversed _ _ _ otherwise => loopControl otherwise
    | _ => false

  /-- Structural recursion keeps finite syntax inspection reducible in proofs. -/
  def loopControl : List Stmt → Bool
    | [] => false
    | head :: tail => loopControlStmt head || loopControl tail
end

/-- Plain loops keep their original continuation; transfers need an explicit
boundary so flattening an `if` cannot erase the nearest loop's exit point. -/
def loopContinuation (body : List Stmt) (next : Stmt) : Stmt :=
  if loopControl body then .loopResume next else next

/-- Only entered loops have boundaries in the pending instruction list. -/
def loopTarget : List Stmt → Option (Stmt × List Stmt)
  | [] => none
  | .loopResume next :: rest => some (next, rest)
  | _ :: rest => loopTarget rest

private def rangeState (name : String) (env : ScalarEnv) (done : List Constant)
    (expressions : List Expr) (body otherwise following : List Stmt) (stack : List Frame) : State :=
  match expressions with
  | [] => ⟨.startRange name done body otherwise following env, stack⟩
  | first :: rest =>
      ⟨.expr first env, .rangeArguments name done rest body otherwise following env :: stack⟩

private def sumState (name : String) (element : Expr) (conditions : List Expr)
    (env : ScalarEnv) (done : List Constant) (expressions : List Expr) (stack : List Frame) : State :=
  match expressions with
  | [] => ⟨.startSum name element conditions done env, stack⟩
  | first :: rest =>
      ⟨.expr first env, .sumArguments name element conditions done rest env :: stack⟩

private def extremumState (maximum : Bool) (key : String) (env : ScalarEnv)
    (done : List Constant) (expressions : List Expr) (stack : List Frame) : State :=
  match expressions with
  | [] => ⟨.startExtremum maximum key done, stack⟩
  | first :: rest =>
      ⟨.expr first env, .extremumArguments maximum key done rest env :: stack⟩

/-- Sum accepts booleans as integers; strings and None cause TypeError. -/
def sumAdd (total : Int) : Constant → Except ExceptionObject Int
  | .int n => .ok (total + n)
  | .bool b => .ok (total + if b then 1 else 0)
  | _ => .error { typeName := "TypeError", args := [] }

def step (module : Module) (state : State) : Step State Constant :=
  let ⟨work, stack⟩ := state
  match work with
  | .primitive operation values => outcome (operation.apply values) stack
  | .startRange name values body otherwise following env =>
      match rangeBounds values with
      | .ok (start, stop, stride) =>
          .next ⟨.block (.rangeStepLoop name start stop stride body otherwise :: following) env, stack⟩
      | .error exception => .done (.error exception)
  | .startSum name element conditions values env =>
      match rangeBounds values with
      | .ok (start, stop, stride) =>
          .next ⟨.sumLoop ⟨name, element, conditions, stop, stride, env⟩ start 0, stack⟩
      | .error exception => .done (.error exception)
  | .sumLoop sum next total =>
      if rangeContinues next sum.stop sum.stride then
        .next ⟨.expr sum.filter (sum.env.set sum.name (.int next)), .sumFilter sum next total :: stack⟩
      else .next ⟨.value (.int total), stack⟩
  | .startExtremum maximum key values =>
      match rangeBounds values with
      | .ok (start, stop, stride) =>
          .next ⟨.extremumLoop ⟨maximum, key, stop, stride⟩ start none, stack⟩
      | .error exception => .done (.error exception)
  | .extremumLoop range next best =>
      if rangeContinues next range.stop range.stride then
        .next ⟨.invoke range.key [.int next], .extremumKey range next best :: stack⟩
      else match best with
        | some (winner, _) => .next ⟨.value (.int winner), stack⟩
        | none => .done (.error { typeName := "ValueError", args := [] })
  | .invoke name values =>
      match findFunctionIn module.body name with
      | some (args, body) =>
          if args.length = values.length then
            .next ⟨.block (executableBody body) (argumentEnv args values), stack⟩
          else match completeArguments args values with
            | some values => .next ⟨.block (executableBody body) (argumentEnv args values), stack⟩
            | none => .done (.error { typeName := "TypeError", args := [] })
      | none => outcome (libraryCall module name values) stack
  | .expr expression env =>
      match expression with
      | .builtinCall builtin args => .next (primitiveState (.builtin builtin) env [] args stack)
      | .subscript value (.slice lower upper stride) =>
          .next (primitiveState .slice env [] [value, lower.getD (.constant .none),
            upper.getD (.constant .none), stride.getD (.constant .none)] stack)
      | .subscript value index => .next (primitiveState .subscript env [] [value, index] stack)
      | .extremumRange maximum bounds key =>
          .next (extremumState maximum key env [] bounds stack)
      | .sumRange name element bounds conditions =>
          .next (sumState name element conditions env [] bounds stack)
      | .constant value => .next ⟨.value value, stack⟩
      | .name name => outcome (Except.ok <$> env name) stack
      | .binOp left op right =>
          .next ⟨.expr left env, .binaryLeft op right env :: stack⟩
      | .unaryOp op expr => .next ⟨.expr expr env, .unary op :: stack⟩
      | .compare left [(op, right)] =>
          .next ⟨.expr left env, .compareLeft op right env :: stack⟩
      | .compare left ((op, right) :: rest) =>
          .next ⟨.expr left env, .chainLeft op right rest env :: stack⟩
      | .boolOp _ [] => .unsupported
      | .boolOp op (first :: rest) =>
          .next ⟨.expr first env, .boolean op rest env :: stack⟩
      | .ifExp test yes no => .next ⟨.expr test env, .conditional yes no env :: stack⟩
      | .call (.name name) [] => .next ⟨.invoke name [], stack⟩
      | .call (.name name) (first :: rest) =>
          .next ⟨.expr first env, .arguments name [] rest env :: stack⟩
      | .call (.attribute (.name name) field) args =>
          .next ⟨.expr (.call (.name (name ++ "." ++ field)) args) env, stack⟩
      | _ => .unsupported
  | .block body env =>
      match body with
      | [] => .next ⟨.value .none, stack⟩
      | .return expr :: _ => .next ⟨.expr expr env, stack⟩
      | .raise (some (.call (.name typeName) args)) :: _ =>
          .next (primitiveState (.raiseException typeName) env [] args stack)
      | .raise (some (.name typeName)) :: _ =>
          .next (primitiveState (.raiseException typeName) env [] [] stack)
      | .assign [.name name] expr :: rest =>
          .next ⟨.expr expr env, .assign name rest env :: stack⟩
      | .annAssign (.name name) _ (some expr) :: rest =>
          .next ⟨.expr expr env, .assign name rest env :: stack⟩
      | .annAssign (.name _) _ none :: rest => .next ⟨.block rest env, stack⟩
      | .assign [.tuple targets] (.tuple expressions) :: rest =>
          match targetNames targets with
          | none => .unsupported
          | some names =>
              if names.length = expressions.length then
                match expressions with
                | [] => .next ⟨.block rest env, stack⟩
                | first :: tail =>
                    .next ⟨.expr first env, .unpack names [] tail rest env :: stack⟩
              else .unsupported
      | .augAssign (.name name) op expr :: rest =>
          .next ⟨.expr (.binOp (.name name) op expr) env, .assign name rest env :: stack⟩
      | .assert condition message :: rest =>
          .next ⟨.expr condition env, .assertion message rest env :: stack⟩
      | .ifThen condition yes no :: rest =>
          .next ⟨.expr condition env, .branch yes no rest env :: stack⟩
      | .whileDo condition body otherwise :: rest =>
          .next ⟨.expr condition env,
            .branch (body ++ [loopContinuation body (.whileDo condition body otherwise)]) otherwise rest env :: stack⟩
      | .loopResume next :: rest => .next ⟨.block (next :: rest) env, stack⟩
      | .breakLoop :: rest =>
          match loopTarget rest with
          | some (_, following) => .next ⟨.block following env, stack⟩
          | none => .unsupported
      | .continueLoop :: rest =>
          match loopTarget rest with
          | some (next, following) => .next ⟨.block (next :: following) env, stack⟩
          | none => .unsupported
      | .forIn (.name name) (.call (.name "range") expressions) body otherwise :: rest =>
          .next (rangeState name env [] expressions body otherwise rest stack)
      | .rangeStepLoop name next stop stride body otherwise :: rest =>
          if rangeContinues next stop stride then
            .next ⟨.block (body ++ [loopContinuation body (.rangeStepLoop name (next + stride) stop stride body otherwise)] ++ rest)
              (env.set name (.int next)), stack⟩
          else .next ⟨.block (otherwise ++ rest) env, stack⟩
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
          | .chainLeft op right rest env =>
              .next ⟨.expr right env, .chainRight op value rest env :: stack⟩
          | .chainRight op left rest env =>
              match scalarCompare op left value with
              | none => .unsupported
              | some false => .next ⟨.value (.bool false), stack⟩
              | some true => match rest with
                  | [] => .next ⟨.value (.bool true), stack⟩
                  | (op, right) :: rest =>
                      .next ⟨.expr right env, .chainRight op value rest env :: stack⟩
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
          | .primitiveArguments operation done rest env =>
              .next (primitiveState operation env (done ++ [value]) rest stack)
          | .assign name rest env => .next ⟨.block rest (env.set name value), stack⟩
          | .branch yes no rest env =>
              .next ⟨.block ((if scalarTruth value then yes else no) ++ rest) env, stack⟩
          | .assertion message rest env =>
              if scalarTruth value then .next ⟨.block rest env, stack⟩
              else match message with
                | none => .done (.error { typeName := "AssertionError", args := [] })
                | some expression => .next ⟨.expr expression env, .assertionMessage :: stack⟩
          | .assertionMessage => .done (.error { typeName := "AssertionError", args := [value] })
          | .discard rest env => .next ⟨.block rest env, stack⟩
          | .unpack names done rest body env =>
              match rest with
              | [] => .next ⟨.block body (assignNames env names (done ++ [value])), stack⟩
              | first :: tail =>
                  .next ⟨.expr first env, .unpack names (done ++ [value]) tail body env :: stack⟩
          | .extremumArguments maximum key done rest env =>
              .next (extremumState maximum key env (done ++ [value]) rest stack)
          | .extremumKey range next best =>
              match range.choose next value best with
              | .ok best => .next ⟨.extremumLoop range (next + range.stride) (some best), stack⟩
              | .error exception => .done (.error exception)
          | .sumArguments name element conditions done rest env =>
              .next (sumState name element conditions env (done ++ [value]) rest stack)
          | .sumFilter sum next total =>
              if scalarTruth value then
                .next ⟨.expr sum.element (sum.env.set sum.name (.int next)), .sumElement sum next total :: stack⟩
              else .next ⟨.sumLoop sum (next + sum.stride) total, stack⟩
          | .sumElement sum next total =>
              match sumAdd total value with
              | .ok total => .next ⟨.sumLoop sum (next + sum.stride) total, stack⟩
              | .error exception => .done (.error exception)
          | .rangeArguments name done rest body otherwise following env =>
              .next (rangeState name env (done ++ [value]) rest body otherwise following stack)

def function (module : Module) (name : String) (args : List Constant) : Execution Constant :=
  ⟨State, ⟨.invoke name args, []⟩, step module⟩

/-- Execute a Python expression in its input environment, including helper calls. -/
def evaluate (module : Module) (env : ScalarEnv) (expr : Expr) : Execution Constant :=
  ⟨State, ⟨.expr expr env, []⟩, step module⟩

/-- A precondition holds only when evaluation returns Boolean True, not a truthy
integer or string. Exceptions and nontermination do not satisfy the condition. -/
def Condition (module : Module) (env : ScalarEnv) (expr : Expr) : Prop :=
  Finishes (evaluate module env expr).step (evaluate module env expr).initial (.ok (.bool true))

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

theorem Evaluates.finishes (h : Evaluates module env expr value) :
    Finishes (evaluate module env expr).step (evaluate module env expr).initial (.ok value) :=
  (h []).finishes (.done rfl)

theorem Evaluates.condition_iff (h : Evaluates module env expr value) :
    Condition module env expr ↔ value = .bool true := by
  constructor
  · intro holds
    exact Except.ok.inj (h.finishes.unique holds)
  · intro equal
    subst value
    exact h.finishes

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

theorem unary (operand : Evaluates module env expression value)
    (result : scalarExpr (fun _ => none) (.unaryOp op (.constant value)) = some (.ok answer)) :
    Evaluates module env (.unaryOp op expression) answer := by
  intro stack
  exact .next rfl ((operand _).trans (.next (by simp [step, outcome, result]) .refl))

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

theorem library_call (arguments : Arguments module env expressions values)
    (absent : findFunctionIn module.body name = none)
    (result : libraryCall module name values = some (.ok value)) :
    Evaluates module env (.call (.name name) expressions) value := by
  apply call arguments
  intro stack
  exact .next (by simp [step, absent, outcome, result]) .refl

theorem qualified_call
    (evaluated : Evaluates module env (.call (.name (alias ++ "." ++ field)) expressions) value) :
    Evaluates module env (.call (.attribute (.name alias) field) expressions) value := by
  intro stack
  exact .next rfl (evaluated stack)

private theorem primitive_arguments_reach
    (h : Arguments module env expressions values) (done : List Constant) (stack : List Frame) :
    Reaches module (primitiveState operation env done expressions stack)
      ⟨.primitive operation (done ++ values), stack⟩ := by
  induction h generalizing done with
  | nil => simp [primitiveState]; exact .refl
  | @cons expression value expressions values head tail ih =>
      apply (head _).trans
      refine .next rfl ?_
      simpa [List.append_assoc] using ih (done ++ [value])

private theorem primitive_result (arguments : Arguments module env expressions values)
    (result : operation.apply values = some (.ok value)) (stack : List Frame) :
    Reaches module (primitiveState operation env [] expressions stack) ⟨.value value, stack⟩ :=
  (primitive_arguments_reach arguments [] stack).trans
    (.next (by simpa [step, outcome] using congrArg (fun r => outcome r stack) result) .refl)

theorem builtin (arguments : Arguments module env expressions values)
    (result : (Primitive.builtin operation).apply values = some (.ok value)) :
    Evaluates module env (.builtinCall operation expressions) value :=
  fun stack => .next rfl (primitive_result arguments result stack)

theorem subscript (receiver : Evaluates module env expression value)
    (index : Evaluates module env key indexValue)
    (notSlice : ∀ lower upper stride, key ≠ .slice lower upper stride)
    (result : Strings.get value indexValue = .ok element) :
    Evaluates module env (.subscript expression key) element := by
  intro stack
  apply Reaches.next (following := primitiveState .subscript env [] [expression, key] stack)
  · cases key <;> simp_all [step]
  · exact primitive_result (operation := .subscript)
      (.cons receiver (.cons index .nil)) (congrArg some result) stack

theorem slice (arguments : Arguments module env [expression, lower.getD (.constant .none),
      upper.getD (.constant .none), stride.getD (.constant .none)] [value, start, stop, stepValue])
    (result : Strings.slice value start stop stepValue = .ok sliced) :
    Evaluates module env (.subscript expression (.slice lower upper stride)) sliced :=
  fun stack => .next rfl (primitive_result (operation := .slice) arguments (congrArg some result) stack)

/-- Recover a mathematical comparison from a simple Python input precondition. -/
theorem condition_int_compare
    (holds : Condition module env (.compare (.name name) [(op, .constant (.int bound))]))
    (lookup : env name = some (.int input)) : evalCmpOp op input bound = true := by
  have run : Evaluates module env (.compare (.name name) [(op, .constant (.int bound))])
      (.bool (evalCmpOp op input bound)) :=
    compare (Evaluates.lookup lookup) constant rfl
  simpa using run.condition_iff.mp holds

end Evaluates

/-- A finite generator reduction, compositional in the consumer's continuation. -/
def SumReturns (module : Module) (sum : RangeSum) (next total result : Int) : Prop :=
  ∀ stack, Reaches module ⟨.sumLoop sum next total, stack⟩ ⟨.value (.int result), stack⟩

namespace SumReturns

theorem done (finished : rangeContinues next sum.stop sum.stride = false) :
    SumReturns module sum next total total := by
  intro stack
  exact .next (by simp [step, finished]) .refl

theorem skip (continues : rangeContinues next sum.stop sum.stride = true)
    (test : Evaluates module (sum.env.set sum.name (.int next)) sum.filter value)
    (rejected : scalarTruth value = false)
    (rest : SumReturns module sum (next + sum.stride) total result) :
    SumReturns module sum next total result := by
  intro stack
  exact .next (by simp [step, continues]) ((test (.sumFilter sum next total :: stack)).trans
    (.next (by simp [step, rejected]) (rest stack)))

theorem keep (continues : rangeContinues next sum.stop sum.stride = true)
    (test : Evaluates module (sum.env.set sum.name (.int next)) sum.filter value)
    (accepted : scalarTruth value = true)
    (element : Evaluates module (sum.env.set sum.name (.int next)) sum.element item)
    (addition : sumAdd total item = .ok updated)
    (rest : SumReturns module sum (next + sum.stride) updated result) :
    SumReturns module sum next total result := by
  intro stack
  exact .next (by simp [step, continues]) ((test (.sumFilter sum next total :: stack)).trans
    (.next (by simp [step, accepted]) ((element (.sumElement sum next total :: stack)).trans
      (.next (by simp [step, addition]) (rest stack)))))

end SumReturns

private theorem sum_reach
    (h : Evaluates.Arguments module env expressions values) (done : List Constant)
    (stack : List Frame) :
    Reaches module (sumState name element conditions env done expressions stack)
      ⟨.startSum name element conditions (done ++ values) env, stack⟩ := by
  induction h generalizing done with
  | nil => simp [sumState]; exact .refl
  | @cons expression value expressions values head tail ih =>
      apply (head _).trans
      refine .next rfl ?_
      simpa [List.append_assoc] using ih (done ++ [value])

theorem Evaluates.sum_range (arguments : Evaluates.Arguments module env expressions values)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (rest : SumReturns module ⟨name, element, conditions, stop, stride, env⟩ start 0 result) :
    Evaluates module env (.sumRange name element expressions conditions) (.int result) := by
  intro stack
  exact .next rfl ((sum_reach arguments [] stack).trans
    (.next (by simp [step, bounds]) (rest stack)))


/-- A range reduction that retains the element with the most extreme key. -/
def ExtremumReturns (module : Module) (range : RangeExtremum) (next : Int)
    (best : Option (Int × Constant)) (result : Int) : Prop :=
  ∀ stack, Reaches module ⟨.extremumLoop range next best, stack⟩ ⟨.value (.int result), stack⟩

namespace ExtremumReturns

theorem done (finished : rangeContinues next range.stop range.stride = false) :
    ExtremumReturns module range next (some (winner, score)) winner := by
  intro stack
  exact .next (by simp [step, finished]) .refl

theorem next (continues : rangeContinues current range.stop range.stride = true)
    (key : ReturnsValue module range.key [.int current] score)
    (selected : range.choose current score best = .ok updated)
    (rest : ExtremumReturns module range (current + range.stride) (some updated) result) :
    ExtremumReturns module range current best result := by
  intro stack
  exact .next (by simp [step, continues]) ((key (.extremumKey range current best :: stack)).trans
    (.next (by simp [step, selected]) (rest stack)))

end ExtremumReturns

private theorem extremum_reach
    (h : Evaluates.Arguments module env expressions values) (done : List Constant)
    (stack : List Frame) :
    Reaches module (extremumState maximum key env done expressions stack)
      ⟨.startExtremum maximum key (done ++ values), stack⟩ := by
  induction h generalizing done with
  | nil => simp [extremumState]; exact .refl
  | @cons expression value expressions values head tail ih =>
      apply (head _).trans
      refine .next rfl ?_
      simpa [List.append_assoc] using ih (done ++ [value])

theorem Evaluates.extremum_range (arguments : Evaluates.Arguments module env expressions values)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (rest : ExtremumReturns module ⟨maximum, key, stop, stride⟩ start none result) :
    Evaluates module env (.extremumRange maximum expressions key) (.int result) := by
  intro stack
  exact .next rfl ((extremum_reach arguments [] stack).trans
    (.next (by simp [step, bounds]) (rest stack)))

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

theorem annAssign (h : Evaluates module env expression value)
    (rest : BlockReturns module (env.set name value) body result) :
    BlockReturns module env (.annAssign (.name name) annotation (some expression) :: body) result := by
  intro stack
  exact .next rfl ((h _).trans (.next rfl (rest stack)))

theorem annotation (annotation : Expr) (rest : BlockReturns module env body result) :
    BlockReturns module env (.annAssign (.name name) annotation none :: body) result :=
  fun stack => .next rfl (rest stack)

theorem augAssign (h : Evaluates module env (.binOp (.name name) op expression) value)
    (rest : BlockReturns module (env.set name value) body result) :
    BlockReturns module env (.augAssign (.name name) op expression :: body) result := by
  intro stack
  exact .next rfl ((h _).trans (.next rfl (rest stack)))

/-- A successful assertion continues without evaluating its optional message. -/
theorem assertion (h : Evaluates module env condition value)
    (truth : scalarTruth value = true)
    (rest : BlockReturns module env body result) :
    BlockReturns module env (.assert condition message :: body) result := by
  intro stack
  exact .next rfl ((h _).trans (.next (by simp [step, truth]) (rest stack)))

theorem branch (h : Evaluates module env condition value)
    (rest : BlockReturns module env ((if scalarTruth value then yes else no) ++ body) result) :
    BlockReturns module env (.ifThen condition yes no :: body) result := by
  intro stack
  exact .next rfl ((h _).trans (.next rfl (rest stack)))

theorem while_loop (h : Evaluates module env condition value)
    (rest : BlockReturns module env
      ((if scalarTruth value then loop ++ [loopContinuation loop (.whileDo condition loop otherwise)] else otherwise)
        ++ body) result) :
    BlockReturns module env (.whileDo condition loop otherwise :: body) result := by
  intro stack
  exact .next rfl ((h _).trans (.next rfl (rest stack)))

private theorem range_reach
    (h : Evaluates.Arguments module env expressions values) (done : List Constant)
    (stack : List Frame) :
    Reaches module (rangeState name env done expressions body otherwise following stack)
      ⟨.startRange name (done ++ values) body otherwise following env, stack⟩ := by
  induction h generalizing done with
  | nil => simp [rangeState]; exact .refl
  | @cons expression value expressions values head tail ih =>
      apply (head _).trans
      refine .next rfl ?_
      simpa [List.append_assoc] using ih (done ++ [value])

theorem for_range (arguments : Evaluates.Arguments module env expressions values)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (rest : BlockReturns module env (.rangeStepLoop name start stop stride body otherwise :: following) result) :
    BlockReturns module env (.forIn (.name name) (.call (.name "range") expressions) body otherwise :: following) result := by
  intro stack
  exact .next rfl ((range_reach arguments [] stack).trans
    (.next (by simp [step, bounds]) (rest stack)))

theorem range_step (continues : rangeContinues next stop stride = true)
    (rest : BlockReturns module (env.set name (.int next))
      (body ++ [loopContinuation body (.rangeStepLoop name (next + stride) stop stride body otherwise)] ++ following) result) :
    BlockReturns module env (.rangeStepLoop name next stop stride body otherwise :: following) result := by
  intro stack
  exact .next (by simp [step, continues]) (rest stack)

theorem loop_resume (rest : BlockReturns module env (next :: following) result) :
    BlockReturns module env (.loopResume next :: following) result :=
  fun stack => .next rfl (rest stack)

theorem break_loop (target : loopTarget body = some (next, following))
    (rest : BlockReturns module env following result) :
    BlockReturns module env (.breakLoop :: body) result := by
  intro stack
  exact .next (by simp [step, target]) (rest stack)

theorem continue_loop (target : loopTarget body = some (next, following))
    (rest : BlockReturns module env (next :: following) result) :
    BlockReturns module env (.continueLoop :: body) result := by
  intro stack
  exact .next (by simp [step, target]) (rest stack)

theorem range_done (finished : rangeContinues next stop stride = false)
    (rest : BlockReturns module env (otherwise ++ following) result) :
    BlockReturns module env (.rangeStepLoop name next stop stride body otherwise :: following) result := by
  intro stack
  exact .next (by simp [step, finished]) (rest stack)

private def unpackState (names : List String) (env : ScalarEnv) (done : List Constant)
    (expressions : List Expr) (body : List Stmt) (stack : List Frame) : State :=
  match expressions with
  | [] => ⟨.block body (assignNames env names done), stack⟩
  | first :: tail => ⟨.expr first env, .unpack names done tail body env :: stack⟩

private theorem unpack_reach
    (h : Evaluates.Arguments module env expressions values) (done : List Constant)
    (stack : List Frame) :
    Reaches module (unpackState names env done expressions body stack)
      ⟨.block body (assignNames env names (done ++ values)), stack⟩ := by
  induction h generalizing done with
  | nil => simp [unpackState]; exact .refl
  | @cons expression value expressions values head tail ih =>
      apply (head _).trans
      refine .next (following := unpackState names env (done ++ [value]) expressions body stack) ?_ ?_
      · cases expressions <;> rfl
      · simpa [List.append_assoc] using ih (done ++ [value])

theorem unpack (targets : targetNames expressions = some names)
    (arity : names.length = values.length)
    (h : Evaluates.Arguments module env values results)
    (rest : BlockReturns module (assignNames env names results) body result) :
    BlockReturns module env (.assign [.tuple expressions] (.tuple values) :: body) result := by
  intro stack
  refine .next (following := unpackState names env [] values body stack) ?_ ?_
  · cases values <;> simp [step, targets, arity, unpackState, assignNames]
  · exact (unpack_reach h [] stack).trans (rest stack)

theorem function (found : findFunctionIn module.body name = some (args, body))
    (arity : args.length = values.length)
    (h : BlockReturns module (argumentEnv args values) (executableBody body) value) :
    ReturnsValue module name values value := by
  intro stack
  exact .next (by simp [step, found, arity]) (h stack)

/-- Execute a call that omits one or more trailing default arguments. -/
theorem function_defaults (found : findFunctionIn module.body name = some (args, body))
    (omitted : args.length ≠ values.length)
    (defaults : completeArguments args values = some completed)
    (h : BlockReturns module (argumentEnv args completed) (executableBody body) value) :
    ReturnsValue module name values value := by
  intro stack
  exact .next (by simp [step, found, omitted, defaults]) (h stack)

end BlockReturns

end FormalSW.PyAst.Calls
