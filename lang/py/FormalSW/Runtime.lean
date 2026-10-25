import lang.py.FormalSW.Execution

namespace FormalSW.PyAst

/-- Scalar environments distinguish an unbound name from Python `None`. -/
abbrev ScalarEnv := String → Option Constant

def ScalarEnv.set (env : ScalarEnv) (name : String) (value : Constant) : ScalarEnv :=
  fun query => if query = name then some value else env query

def scalarTruth : Constant → Bool
  | .bool value => value
  | .int value => value != 0
  | .string value => !value.isEmpty
  | .bytes value => !value.isEmpty
  | .none => false

def scalarCompare (op : CmpOp) (left right : Constant) : Option Bool :=
  let number : Constant → Option Int
    | .int value => some value
    | .bool value => some (if value then 1 else 0)
    | _ => none
  match number left, number right with
  | some left, some right => some (evalCmpOp op left right)
  | _, _ => match op with
      | .eq => some (decide (left = right))
      | .notEq => some (decide (left ≠ right))
      | _ => match left, right with
          | .string left, .string right =>
              some (match op with
                | .lt => decide (left < right)
                | .ltE => decide (left ≤ right)
                | .gt => decide (left > right)
                | .gtE => decide (left ≥ right)
                | _ => false)
          | .bytes left, .bytes right =>
              let order := compare left right
              some (match op with
                | .lt => order == .lt
                | .ltE => order != .gt
                | .gt => order == .gt
                | .gtE => order != .lt
                | _ => false)
          | _, _ => none

/-- None and Booleans are singletons. Equal integers, strings and bytes may be
pooled, so their object identity is deliberately left unsupported. -/
def scalarIdentity (left right : Constant) : Option Bool :=
  match left, right with
  | .none, .none => some true
  | .bool a, .bool b => some (a == b)
  | .int a, .int b => if a = b then none else some false
  | .string a, .string b => if a = b then none else some false
  | .bytes a, .bytes b => if a = b then none else some false
  | _, _ => some false

@[simp] def scalarNumber : Constant → Option Int
  | .int n => some n
  | .bool b => some (if b then 1 else 0)
  | _ => none

/-- Boolean conjunction retains bool only when both operands are bool. -/
def scalarBitAnd (left right : Constant) : Except ExceptionObject Constant :=
  match left, right with
  | .bool a, .bool b => .ok (.bool (a && b))
  | _, _ => match scalarNumber left, scalarNumber right with
      | some a, some b => .ok (.int (integerBitAnd a b))
      | _, _ => .error { typeName := "TypeError", args := [] }

/-- Boolean disjunction retains bool only when both operands are bool. -/
def scalarBitOr (left right : Constant) : Except ExceptionObject Constant :=
  match left, right with
  | .bool a, .bool b => .ok (.bool (a || b))
  | _, _ => match scalarNumber left, scalarNumber right with
      | some a, some b => .ok (.int (integerBitOr a b))
      | _, _ => .error { typeName := "TypeError", args := [] }

/-- Exclusive disjunction retains bool only when both operands are bool. -/
def scalarBitXor (left right : Constant) : Except ExceptionObject Constant :=
  match left, right with
  | .bool a, .bool b => .ok (.bool (a != b))
  | _, _ => match scalarNumber left, scalarNumber right with
      | some a, some b => .ok (.int (integerBitXor a b))
      | _, _ => .error { typeName := "TypeError", args := [] }

/-- Shift operands accept integers and Booleans; the result is always an integer. -/
def scalarShiftLeft (left right : Constant) : Except ExceptionObject Constant :=
  match scalarNumber left, scalarNumber right with
  | some a, some b =>
      if b < 0 then .error { typeName := "ValueError", args := [] }
      else .ok (.int (integerShiftLeft a b.toNat))
  | _, _ => .error { typeName := "TypeError", args := [] }

def scalarBinary (op : BinOp) (left right : Constant) : Option (Except ExceptionObject Constant) :=
  match op with
  | .bitAnd => some (scalarBitAnd left right)
  | .bitOr => some (scalarBitOr left right)
  | .bitXor => some (scalarBitXor left right)
  | .leftShift => some (scalarShiftLeft left right)
  | _ =>
    match scalarNumber left, scalarNumber right with
    | some left, some right =>
        match op with
        | .add => some (.ok (.int (left + right)))
        | .sub => some (.ok (.int (left - right)))
        | .mult => some (.ok (.int (left * right)))
        | .bitAnd | .bitOr | .bitXor | .leftShift => none -- Handled before numeric coercion.
        | .pow =>
            if right < 0 then none
            else some (.ok (.int (left ^ right.toNat)))
        | .floorDiv | .mod =>
            if right = 0 then
              some (.error { typeName := "ZeroDivisionError", args := [] })
            else if right > 0 then
              some (.ok (.int (match op with | .mod => left % right | _ => left / right)))
            else
              let quotient := (-left) / (-right)
              some (.ok (.int (match op with | .mod => left - right * quotient | _ => quotient)))
    | _, _ => match op, left, right with
        -- Bytes also use % for formatting, which needs a separate format parser.
        | .mod, .bytes _, _ => none
        | .add, .string a, .string b => some (.ok (.string (a ++ b)))
        | .add, .bytes a, .bytes b => some (.ok (.bytes (a ++ b)))
        | .mult, .bytes text, count | .mult, count, .bytes text =>
            match scalarNumber count with
            | some n => some (.ok (.bytes (List.replicate n.toNat text).flatten))
            | none => some (.error { typeName := "TypeError", args := [] })
        | .mult, .string text, count | .mult, count, .string text =>
            match scalarNumber count with
            | some n => some (.ok (.string (String.join (List.replicate n.toNat text))))
            | none => some (.error { typeName := "TypeError", args := [] })
        | _, _, _ => some (.error { typeName := "TypeError", args := [] })

/-- Supported scalar expressions are finite. Calls and unsupported operators are
rejected; looping Python comparison methods are executed by `comparison` below. -/
def scalarExpr (env : ScalarEnv) : Expr → Option (Except ExceptionObject Constant)
  | .constant value => some (.ok value)
  | .name name => Except.ok <$> env name
  | .attribute (.name name) field => Except.ok <$> env (name ++ "." ++ field)
  | .binOp left op right => do
      let left ← scalarExpr env left
      match left with
      | .error exception => return .error exception
      | .ok left =>
          let right ← scalarExpr env right
          match right with
          | .error exception => return .error exception
          | .ok right => scalarBinary op left right
  | .unaryOp op operand => do
      let operand ← scalarExpr env operand
      match operand with
      | .error exception => return .error exception
      | .ok operand =>
          match op, operand with
          | .not, value => return .ok (.bool (!scalarTruth value))
          | .uSub, .int value => return .ok (.int (-value))
          | .uSub, .bool value => return .ok (.int (if value then -1 else 0))
          | .uSub, _ => return .error { typeName := "TypeError", args := [] }
  | .compare left [(op, right)] => do
      let left ← scalarExpr env left
      match left with
      | .error exception => return .error exception
      | .ok left =>
          let right ← scalarExpr env right
          match right with
          | .error exception => return .error exception
          | .ok right =>
              let result ← scalarCompare op left right
              return .ok (.bool result)
  | _ => none

def scalarException (env : ScalarEnv) : Expr → Option ExceptionObject
  | .call (.name name) args => do
      let values ← args.mapM fun argument => do
        match ← scalarExpr env argument with
        | .ok value => some value
        | .error _ => none
      some { typeName := name, args := values }
  | .name name => some { typeName := name, args := [] }
  | _ => none

structure ScalarState where
  todo : List Stmt
  env : ScalarEnv

/-- Execute one statement or loop guard. No step limit changes the program's result. -/
def scalarStep (state : ScalarState) : Step ScalarState Constant :=
  let ⟨todo, env⟩ := state
  match todo with
  | [] => .done (.ok .none)
  | .return expr :: _ =>
      match scalarExpr env expr with
      | some outcome => .done outcome
      | none => .unsupported
  | .assign [.name name] expr :: rest =>
      match scalarExpr env expr with
      | some (.ok value) => .next ⟨rest, env.set name value⟩
      | some (.error exception) => .done (.error exception)
      | none => .unsupported
  | .augAssign (.name name) op expr :: rest =>
      match scalarExpr env (.binOp (.name name) op expr) with
      | some (.ok value) => .next ⟨rest, env.set name value⟩
      | some (.error exception) => .done (.error exception)
      | none => .unsupported
  | .ifThen condition yes no :: rest =>
      match scalarExpr env condition with
      | some (.ok value) => .next ⟨(if scalarTruth value then yes else no) ++ rest, env⟩
      | some (.error exception) => .done (.error exception)
      | none => .unsupported
  | .whileDo condition body otherwise :: rest =>
      match scalarExpr env condition with
      | some (.ok value) =>
          .next ⟨if scalarTruth value then
            body ++ [.whileDo condition body otherwise] ++ rest
            else otherwise ++ rest, env⟩
      | some (.error exception) => .done (.error exception)
      | none => .unsupported
  | .forIn (.name loopVar) (.call (.name "range") [stop]) body otherwise :: rest =>
      match scalarExpr env stop with
      | some (.ok (.int stop)) => .next ⟨.rangeLoop loopVar 0 stop body otherwise :: rest, env⟩
      | some (.error exception) => .done (.error exception)
      | _ => .unsupported
  | .rangeLoop loopVar next stop body otherwise :: rest =>
      if next < stop then
        .next ⟨body ++ [.rangeLoop loopVar (next + 1) stop body otherwise] ++ rest,
          env.set loopVar (.int next)⟩
      else .next ⟨otherwise ++ rest, env⟩
  | .raise (some expr) :: _ =>
      match scalarException env expr with
      | some exception => .done (.error exception)
      | none => .unsupported
  | .expr expr :: rest =>
      match scalarExpr env expr with
      | some (.ok _) => .next ⟨rest, env⟩
      | some (.error exception) => .done (.error exception)
      | none => .unsupported
  | _ => .unsupported

def scalarBlock (body : List Stmt) (env : ScalarEnv) : Execution Constant :=
  ⟨ScalarState, ⟨executableBody body, env⟩, scalarStep⟩

def findFunctionIn : List Stmt → String → Option (List Arg × List Stmt)
  | [], _ => none
  | .functionDef name args _ body :: rest, query =>
      if query = name then some (args, body) else findFunctionIn rest query
  | _ :: rest, query => findFunctionIn rest query

def argumentEnv (args : List Arg) (values : List Constant) : ScalarEnv :=
  fun name => ((args.map Arg.name).zip values).lookup name

def scalarFunction (module : Module) (name : String) (values : List Constant) : Execution Constant :=
  match findFunctionIn module.body name with
  | some (args, body) =>
      if args.length = values.length then scalarBlock body (argumentEnv args values)
      else Execution.unsupported
  | none => Execution.unsupported

def CmpOp.method : CmpOp → String
  | .eq => "__eq__"
  | .notEq => "__ne__"
  | .lt => "__lt__"
  | .ltE => "__le__"
  | .gt => "__gt__"
  | .gtE => "__ge__"

/-- Custom comparisons run the actual supported method AST, including its loops.
Supported objects are empty or have an integer `value` field. Python reflected comparison and
`NotImplemented` dispatch are not yet modeled; missing methods and comparisons
between objects of different classes or between objects and primitives are unsupported.
-/
def comparison (module : Module) (op : CmpOp) (left right : Value) : Execution Bool :=
  match left, right with
  | .object leftType left, .object rightType right =>
      if leftType = rightType then
        match module.findClassBody leftType with
        | some body =>
            match findFunctionIn body op.method with
            | some ([self, other], body) =>
                let env : ScalarEnv := fun name =>
                  if name = self.name ++ ".value" then left.map Constant.int
                  else if name = other.name ++ ".value" then right.map Constant.int
                  else none
                (scalarBlock body env).bind fun value => Execution.pure (scalarTruth value)
            | _ => Execution.unsupported
        | none => Execution.unsupported
      else Execution.unsupported
  | .object _ _, _ | _, .object _ _ => Execution.unsupported
  | _, _ => Execution.ofExcept (evalValueCmp op left right)

end FormalSW.PyAst

namespace FormalSW.Property.Function

/-- A unary integer function finishes with an integer or a Python exception.
The scalar case uses execution semantics, including arbitrary supported loops.
The CLI separately rejects requirements whose source falls outside the model. -/
def ReturnType (module : PyAst.Module) (name : String) : Prop :=
  match module.findFunctionArgKind name, module.findFunctionReturnKind name with
  | some .int, some .int => ∀ n : Int,
      (∃ value : Int, PyAst.Finishes (PyAst.scalarFunction module name [.int n]).step
        (PyAst.scalarFunction module name [.int n]).initial (.ok (.int value))) ∨
      (PyAst.scalarFunction module name [.int n]).Throws
  | _, _ => AbstractReturnType module name

/-- Successful scalar executions return equal values. -/
def EquivReturn (module : PyAst.Module) (left right : String) : Prop :=
  match module.findFunctionArgKind left, module.findFunctionArgKind right with
  | some .int, some .int => ∀ n leftResult rightResult,
      PyAst.Finishes (PyAst.scalarFunction module left [.int n]).step
        (PyAst.scalarFunction module left [.int n]).initial (.ok leftResult) →
      PyAst.Finishes (PyAst.scalarFunction module right [.int n]).step
        (PyAst.scalarFunction module right [.int n]).initial (.ok rightResult) →
      leftResult = rightResult
  | _, _ => AbstractEquivReturn module left right

/-- Scalar equivalence preserves actual finite execution outcomes, including
exceptions. The older list equivalence model remains an abstraction. -/
def Equiv (module : PyAst.Module) (left right : String) : Prop :=
  match module.findFunctionArgKind left, module.findFunctionArgKind right with
  | some .int, some .int => ∀ n : Int,
      (PyAst.scalarFunction module left [.int n]).Equiv
        (PyAst.scalarFunction module right [.int n])
  | _, _ => AbstractEquiv module left right

end FormalSW.Property.Function
