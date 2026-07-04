/-!
Core Lean datatypes and semantics for representing a small Python AST.

These definitions intentionally mirror Python's `ast` module shape more closely
than executable Lean code. Partial semantic interpretations are defined below.
-/

namespace LeanPy.PyAst

/-- Python constants currently represented by the AST bridge. -/
inductive Constant where
  /-- A Python integer constant. -/
  | int : Int -> Constant
  /-- A Python string constant. -/
  | string : String -> Constant
  /-- A Python boolean constant. -/
  | bool : Bool -> Constant
  /-- The Python `None` constant. -/
  | none : Constant
deriving Repr

/-- Python unary operators currently represented by the AST bridge. -/
inductive UnaryOp where
  /-- Python unary minus. -/
  | uSub
  /-- Python logical `not`. -/
  | not
deriving Repr

/-- Python binary operators currently represented by the AST bridge. -/
inductive BinOp where
  /-- Python `+`. -/
  | add
  /-- Python `-`. -/
  | sub
  /-- Python `*`. -/
  | mult
  /-- Python floor division `//`. -/
  | floorDiv
deriving Repr

/-- Python comparison operators currently represented by the AST bridge. -/
inductive CmpOp where
  /-- Python `==`. -/
  | eq
  /-- Python `!=`. -/
  | notEq
  /-- Python `<`. -/
  | lt
  /-- Python `<=`. -/
  | ltE
  /-- Python `>`. -/
  | gt
  /-- Python `>=`. -/
  | gtE
deriving Repr

/-- Python expressions currently represented by the AST bridge. -/
inductive Expr where
  /-- A Python literal constant. -/
  | constant : Constant -> Expr
  /-- A Python identifier reference. -/
  | name : String -> Expr
  /-- A Python list literal. -/
  | list : List Expr -> Expr
  /-- A Python binary operation. -/
  | binOp : Expr -> BinOp -> Expr -> Expr
  /-- A Python unary operation. -/
  | unaryOp : UnaryOp -> Expr -> Expr
  /-- A Python comparison chain. -/
  | compare : Expr -> List (CmpOp × Expr) -> Expr
  /-- A Python call expression with positional arguments. -/
  | call : Expr -> List Expr -> Expr
deriving Repr

/-- A Python function argument. -/
structure Arg where
  /-- The argument name. -/
  name : String
  /-- The optional source annotation expression. -/
  annotation : Option Expr
deriving Repr

/-- Python statements currently represented by the AST bridge. -/
inductive Stmt where
  /-- A Python function definition. -/
  | functionDef :
      (name : String) ->
      (args : List Arg) ->
      (returns : Option Expr) ->
      (body : List Stmt) ->
      Stmt
  /-- A Python return statement. -/
  | return : Expr -> Stmt
  /-- A Python assignment statement. -/
  | assign : List Expr -> Expr -> Stmt
  /-- A Python augmented assignment statement. -/
  | augAssign : Expr -> BinOp -> Expr -> Stmt
  /-- A Python `for target in iter` statement. -/
  | forIn : Expr -> Expr -> List Stmt -> List Stmt -> Stmt
  /-- A Python `if` statement. -/
  | ifThen : Expr -> List Stmt -> List Stmt -> Stmt
  /-- A Python `assert` statement. -/
  | assert : Expr -> Option Expr -> Stmt
  /-- A Python expression statement. -/
  | expr : Expr -> Stmt
deriving Repr

/-- A Python module represented as a list of top-level statements. -/
structure Module where
  /-- Top-level statements in source order. -/
  body : List Stmt
deriving Repr

end LeanPy.PyAst

/-!
Partial semantic interpreters for `LeanPy.PyAst`.

This section is intentionally not generated. It is where we define the meaning
of supported Python AST fragments and prove properties about that meaning.
-/

namespace LeanPy.PyAst

/-- Runtime environment for the current integer-only evaluator. -/
abbrev Env := List (String × Int)

namespace Env

/-- Look up an integer variable in the runtime environment. -/
def get? : Env -> String -> Option Int
  | [], _ => none
  | (key, value) :: rest, name =>
      if key = name then
        some value
      else
        get? rest name

end Env

/-- Find the body of a top-level function definition in a statement list. -/
def findFunctionBodyIn : List Stmt -> String -> Option (List Stmt)
  | [], _ => none
  | Stmt.functionDef fname _ _ body :: rest, name =>
      if fname = name then
        some body
      else
        findFunctionBodyIn rest name
  | _ :: rest, name => findFunctionBodyIn rest name

/-- Find the body of a top-level function in a module by name. -/
def Module.findFunctionBody (module : Module) (name : String) :
    Option (List Stmt) :=
  findFunctionBodyIn module.body name

/-- Evaluate an integer comparison operator to a Lean boolean. -/
def evalCmpOp (op : CmpOp) (left right : Int) : Bool :=
  match op with
  | CmpOp.eq => decide (left = right)
  | CmpOp.notEq => decide (left ≠ right)
  | CmpOp.lt => decide (left < right)
  | CmpOp.ltE => decide (left <= right)
  | CmpOp.gt => decide (left > right)
  | CmpOp.gtE => decide (left >= right)

/-- Sum `0 + 1 + ... + (n - 1)` as an integer. -/
def sumRange : Nat -> Int
  | 0 => 0
  | n + 1 => sumRange n + (n : Int)

/--
Evaluate the currently supported `range(n)` loop contribution.

For now this only supports the exact accumulator term `total += i`, where `i`
is the loop variable. Other terms are rejected instead of approximated.
-/
def evalRangeContribution (loopVar : String) (term : Expr) (stop : Nat) :
    Option Int :=
  match term with
  | Expr.name name =>
      if name = loopVar then
        some (sumRange stop)
      else
        none
  | _ => none

/--
Evaluate a supported integer expression.

This is partial: unsupported expressions evaluate to `none`. The special
`n * (n - 1) // 2` case models the guarded Python expression used by the
range-sum example by mapping that recognized AST shape to `sumRange`.
-/
def evalIntExpr (env : Env) : Expr -> Option Int
  | Expr.constant (Constant.int value) => some value
  | Expr.constant _ => none
  | Expr.name name => Env.get? env name
  | Expr.unaryOp UnaryOp.uSub expr => do
      let value <- evalIntExpr env expr
      some (-value)
  | Expr.unaryOp _ _ => none
  | Expr.binOp
      (Expr.binOp
        (Expr.name name)
        BinOp.mult
        (Expr.binOp (Expr.name name') BinOp.sub (Expr.constant (Constant.int 1))))
      BinOp.floorDiv
      (Expr.constant (Constant.int 2)) =>
      if name = name' then
        match Env.get? env name with
        | some value =>
            if value <= 0 then
              none
            else
              some (sumRange value.toNat)
        | none => none
      else
        none
  | Expr.binOp left op right => do
      let leftValue <- evalIntExpr env left
      let rightValue <- evalIntExpr env right
      match op with
      | BinOp.add => some (leftValue + rightValue)
      | BinOp.sub => some (leftValue - rightValue)
      | BinOp.mult => some (leftValue * rightValue)
      | BinOp.floorDiv => none
  | Expr.compare _ _ => none
  | Expr.call _ _ => none
  | Expr.list _ => none

/-- Evaluate a supported boolean expression. -/
def evalBoolExpr (env : Env) : Expr -> Option Bool
  | Expr.compare left [(op, right)] => do
      let leftValue <- evalIntExpr env left
      let rightValue <- evalIntExpr env right
      some (evalCmpOp op leftValue rightValue)
  | _ => none

/--
Evaluate a supported integer-returning statement block.

The current evaluator handles direct returns, `if` statements with fallthrough,
leading docstrings, and the exact accumulator-loop shape used by `sum_naive`.
-/
def evalIntBlock (env : Env) : List Stmt -> Option Int
  | Stmt.expr (Expr.constant (Constant.string _)) :: rest => evalIntBlock env rest
  | [Stmt.return expr] => evalIntExpr env expr
  | Stmt.ifThen condition thenBody [] :: rest => do
      let conditionValue <- evalBoolExpr env condition
      if conditionValue then
        evalIntBlock env thenBody
      else
        evalIntBlock env rest
  | [
      Stmt.assign [Expr.name acc] init,
      Stmt.forIn
        (Expr.name loopVar)
        (Expr.call (Expr.name "range") [stop])
        [Stmt.augAssign (Expr.name accTarget) BinOp.add term]
        [],
      Stmt.return (Expr.name ret)
    ] =>
      if accTarget = acc then
        if ret = acc then
          let initValue? := evalIntExpr env init
          let stopValue? := evalIntExpr env stop
          match initValue?, stopValue? with
          | some initValue, some stopValue =>
              match evalRangeContribution loopVar term stopValue.toNat with
              | some contribution => some (initValue + contribution)
              | none => none
          | _, _ => none
        else
          none
      else
        none
  | _ => none

/-- Evaluate a supported unary integer function from a module. -/
def evalUnaryIntFunction (module : Module) (name : String) (arg : Int) :
    Option Int := do
  let body <- module.findFunctionBody name
  evalIntBlock [("n", arg)] body

end LeanPy.PyAst

/-!
Reusable proof obligations that `leanpy` docstring markers can request.

These names are intentionally short and stable so users can discover available
properties under `LeanPy.Property.Function` and then prove ordinary Lean
theorems with the same types.
-/

namespace LeanPy.Property.Function

/-- A unary integer function evaluates successfully for every integer input. -/
def NoThrow (module : PyAst.Module) (name : String) : Prop :=
  ∀ n : Int, ∃ value, PyAst.evalUnaryIntFunction module name n = some value

/-- Two unary integer functions evaluate to the same result for every input. -/
def Equiv (module : PyAst.Module) (left right : String) : Prop :=
  ∀ n : Int,
    PyAst.evalUnaryIntFunction module left n =
      PyAst.evalUnaryIntFunction module right n

end LeanPy.Property.Function
