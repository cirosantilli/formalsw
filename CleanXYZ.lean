import Lean

/-!
Core Lean datatypes and semantics for representing a small Python AST.

These definitions intentionally mirror Python's `ast` module shape more closely
than executable Lean code. Partial semantic interpretations are defined below.
-/

namespace CleanXYZ.PyAst

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
deriving Repr, DecidableEq, Lean.ToExpr

/-- Python unary operators currently represented by the AST bridge. -/
inductive UnaryOp where
  /-- Python unary minus. -/
  | uSub
  /-- Python logical `not`. -/
  | not
deriving Repr, Lean.ToExpr

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
  /-- Python remainder `%`. -/
  | mod
deriving Repr, Lean.ToExpr

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
deriving Repr, Lean.ToExpr

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
deriving Repr, Lean.ToExpr

/-- A Python function argument. -/
structure Arg where
  /-- The argument name. -/
  name : String
  /-- The optional source annotation expression. -/
  annotation : Option Expr
deriving Repr, Lean.ToExpr

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
  /-- A Python `raise` statement. -/
  | raise : Option Expr -> Stmt
  /-- A Python expression statement. -/
  | expr : Expr -> Stmt
deriving Repr, Lean.ToExpr

/-- A Python module represented as a list of top-level statements. -/
structure Module where
  /-- Top-level statements in source order. -/
  body : List Stmt
deriving Repr, Lean.ToExpr

/-- A modeled Python exception object. -/
structure ExceptionObject where
  /-- Exception class name, such as `ValueError`. -/
  typeName : String
  /-- Evaluated positional constructor arguments. -/
  args : List Constant
deriving Repr, DecidableEq

/-- A successful return value or a thrown exception object. -/
abbrev Outcome := Except ExceptionObject Int

/-- Read a required field from a JSON object. -/
private def jsonField (json : Lean.Json) (name : String) : Except String Lean.Json :=
  json.getObjVal? name

/-- Read a required string field from a JSON object. -/
private def jsonString (json : Lean.Json) (name : String) : Except String String := do
  (← jsonField json name).getStr?

/-- Read a required array field and decode each of its elements. -/
private def jsonArray (json : Lean.Json) (name : String)
    (decode : Lean.Json → Except String α) : Except String (List α) := do
  let values ← (← jsonField json name).getArr?
  values.toList.mapM decode

/-- Decode a unary operator name from the JSON schema. -/
private def UnaryOp.fromJson? (json : Lean.Json) : Except String UnaryOp := do
  match ← json.getStr? with
  | "USub" => return .uSub
  | "Not" => return .not
  | name => throw s!"unsupported unary operator: {name}"

/-- Decode a binary operator name from the JSON schema. -/
private def BinOp.fromJson? (json : Lean.Json) : Except String BinOp := do
  match ← json.getStr? with
  | "Add" => return .add
  | "Sub" => return .sub
  | "Mult" => return .mult
  | "FloorDiv" => return .floorDiv
  | "Mod" => return .mod
  | name => throw s!"unsupported binary operator: {name}"

/-- Decode a comparison operator name from the JSON schema. -/
private def CmpOp.fromJson? (json : Lean.Json) : Except String CmpOp := do
  match ← json.getStr? with
  | "Eq" => return .eq
  | "NotEq" => return .notEq
  | "Lt" => return .lt
  | "LtE" => return .ltE
  | "Gt" => return .gt
  | "GtE" => return .gtE
  | name => throw s!"unsupported comparison operator: {name}"

/-- Decode one expression from the version 1 JSON schema. -/
private partial def Expr.fromJson? (json : Lean.Json) : Except String Expr := do
  match ← jsonString json "type" with
  | "Constant" =>
      match ← jsonField json "value" with
      | .num number => return .constant (.int (← (Lean.Json.num number).getInt?))
      | .str value => return .constant (.string value)
      | .bool value => return .constant (.bool value)
      | .null => return .constant .none
      | _ => throw "unsupported Constant.value"
  | "Name" => return .name (← jsonString json "id")
  | "List" => return .list (← jsonArray json "elts" Expr.fromJson?)
  | "BinOp" =>
      return .binOp
        (← Expr.fromJson? (← jsonField json "left"))
        (← BinOp.fromJson? (← jsonField json "op"))
        (← Expr.fromJson? (← jsonField json "right"))
  | "UnaryOp" =>
      return .unaryOp
        (← UnaryOp.fromJson? (← jsonField json "op"))
        (← Expr.fromJson? (← jsonField json "operand"))
  | "Compare" =>
      let operators ← jsonArray json "ops" CmpOp.fromJson?
      let comparators ← jsonArray json "comparators" Expr.fromJson?
      if operators.length != comparators.length then
        throw "Compare.ops and Compare.comparators must have equal lengths"
      return .compare
        (← Expr.fromJson? (← jsonField json "left"))
        (operators.zip comparators)
  | "Call" =>
      return .call
        (← Expr.fromJson? (← jsonField json "func"))
        (← jsonArray json "args" Expr.fromJson?)
  | type => throw s!"unsupported expression type: {type}"

/-- Decode a nullable expression field from a JSON object. -/
private def optionalExpr (json : Lean.Json) (name : String) : Except String (Option Expr) := do
  match ← jsonField json name with
  | .null => return none
  | value => return some (← Expr.fromJson? value)

/-- Decode one function argument from the version 1 JSON schema. -/
private def Arg.fromJson? (json : Lean.Json) : Except String Arg := do
  return {
    name := ← jsonString json "name"
    annotation := ← optionalExpr json "annotation"
  }

/-- Decode one statement from the version 1 JSON schema. -/
private partial def Stmt.fromJson? (json : Lean.Json) : Except String Stmt := do
  match ← jsonString json "type" with
  | "FunctionDef" =>
      return .functionDef
        (← jsonString json "name")
        (← jsonArray json "args" Arg.fromJson?)
        (← optionalExpr json "returns")
        (← jsonArray json "body" Stmt.fromJson?)
  | "Return" => return .return (← Expr.fromJson? (← jsonField json "value"))
  | "Assign" =>
      return .assign
        (← jsonArray json "targets" Expr.fromJson?)
        (← Expr.fromJson? (← jsonField json "value"))
  | "AugAssign" =>
      return .augAssign
        (← Expr.fromJson? (← jsonField json "target"))
        (← BinOp.fromJson? (← jsonField json "op"))
        (← Expr.fromJson? (← jsonField json "value"))
  | "For" =>
      return .forIn
        (← Expr.fromJson? (← jsonField json "target"))
        (← Expr.fromJson? (← jsonField json "iter"))
        (← jsonArray json "body" Stmt.fromJson?)
        (← jsonArray json "orelse" Stmt.fromJson?)
  | "If" =>
      return .ifThen
        (← Expr.fromJson? (← jsonField json "test"))
        (← jsonArray json "body" Stmt.fromJson?)
        (← jsonArray json "orelse" Stmt.fromJson?)
  | "Assert" =>
      return .assert
        (← Expr.fromJson? (← jsonField json "test"))
        (← optionalExpr json "msg")
  | "Raise" => return .raise (← optionalExpr json "exc")
  | "Expr" => return .expr (← Expr.fromJson? (← jsonField json "value"))
  | type => throw s!"unsupported statement type: {type}"

/--
Decode a complete cleanxyz JSON AST document.

The schema version is checked before the JSON data is turned into the typed
`PyAst.Module` on which proofs operate.
-/
def Module.fromJsonDocument? (json : Lean.Json) : Except String Module := do
  let version ← (← jsonField json "schema_version").getNat?
  if version != 1 then
    throw s!"unsupported cleanxyz AST schema version: {version}"
  let ast ← jsonField json "ast"
  if (← jsonString ast "type") != "Module" then
    throw "the top-level AST node must have type Module"
  return { body := ← jsonArray ast "body" Stmt.fromJson? }

end CleanXYZ.PyAst

/-- Import a cleanxyz JSON AST as a reducible, typed `CleanXYZ.PyAst.Module`. -/
syntax "pyast_from_json% " term : term

open Lean Elab Term Meta in
elab_rules : term
  | `(pyast_from_json% $jsonSource:term) => do
      let sourceExpr ← elabTerm jsonSource (some (mkConst ``String))
      let some source := getStringValue? sourceExpr
        | throwError "pyast_from_json% expects a string literal, usually from include_str"
      let json ← match Json.parse source with
        | .ok value => pure value
        | .error message => throwError "invalid cleanxyz AST JSON: {message}"
      let module ← match CleanXYZ.PyAst.Module.fromJsonDocument? json with
        | .ok value => pure value
        | .error message => throwError "invalid cleanxyz AST document: {message}"
      return Lean.toExpr module

/-!
Partial semantic interpreters for `CleanXYZ.PyAst`.

This section is intentionally not generated. It is where we define the meaning
of supported Python AST fragments and prove properties about that meaning.
-/

namespace CleanXYZ.PyAst

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
      | BinOp.mod => if rightValue = 0 then none else some (leftValue % rightValue)
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

The current evaluator handles direct returns, explicit `raise` failure, `if`
statements with fallthrough, leading docstrings, and the exact accumulator-loop
shape used by `sum_naive`.
-/
def evalIntBlock (env : Env) : List Stmt -> Option Int
  | Stmt.expr (Expr.constant (Constant.string _)) :: rest => evalIntBlock env rest
  | Stmt.raise _ :: _ => none
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

/-- Evaluate a supported exception-constructor argument. -/
def evalExceptionArg (env : Env) : Expr → Option Constant
  | Expr.constant value => some value
  | Expr.name name => Constant.int <$> Env.get? env name
  | expr => Constant.int <$> evalIntExpr env expr

/-- Evaluate a supported Python exception object construction. -/
def evalExceptionObject (env : Env) : Expr → Option ExceptionObject
  | Expr.call (Expr.name typeName) args => do
      let args ← args.mapM (evalExceptionArg env)
      some { typeName, args }
  | Expr.name typeName => some { typeName, args := [] }
  | _ => none

/--
Evaluate a statement block while preserving returned values and thrown objects.

`none` is reserved for AST shapes outside the current partial semantics, so two
unsupported evaluations are not considered equivalent outcomes.
-/
def evalIntBlockOutcome (env : Env) : List Stmt → Option Outcome
  | Stmt.expr (Expr.constant (Constant.string _)) :: rest =>
      evalIntBlockOutcome env rest
  | Stmt.raise (some exception) :: _ =>
      Except.error <$> evalExceptionObject env exception
  | Stmt.raise none :: _ => none
  | [Stmt.return expr] => Except.ok <$> evalIntExpr env expr
  | Stmt.ifThen condition thenBody [] :: rest => do
      let conditionValue ← evalBoolExpr env condition
      if conditionValue then
        evalIntBlockOutcome env thenBody
      else
        evalIntBlockOutcome env rest
  | statements => Except.ok <$> evalIntBlock env statements

/-- Evaluate a supported unary integer function from a module. -/
def evalUnaryIntFunction (module : Module) (name : String) (arg : Int) :
    Option Int := do
  let body <- module.findFunctionBody name
  evalIntBlock [("n", arg)] body

/-- Evaluate a unary integer function while preserving thrown exception objects. -/
def evalUnaryIntFunctionOutcome (module : Module) (name : String) (arg : Int) :
    Option Outcome := do
  let body ← module.findFunctionBody name
  evalIntBlockOutcome [("n", arg)] body

end CleanXYZ.PyAst

/-!
Reusable proof obligations that `cleanxyz` docstring markers can request.

These names are intentionally short and stable so users can discover available
properties under `CleanXYZ.Property.Function` and then prove ordinary Lean
theorems with the same types.
-/

namespace CleanXYZ.Property.Function

/-- A unary integer function throws a modeled exception for at least one input. -/
def Throws (module : PyAst.Module) (name : String) : Prop :=
  ∃ n : Int, ∃ exception,
    PyAst.evalUnaryIntFunctionOutcome module name n = some (.error exception)

/--
Two unary integer functions return the same value or throw structurally equal
exception objects for every input.
-/
def Equiv (module : PyAst.Module) (left right : String) : Prop :=
  ∀ n : Int, ∃ outcome,
    PyAst.evalUnaryIntFunctionOutcome module left n = some outcome ∧
      PyAst.evalUnaryIntFunctionOutcome module right n = some outcome

end CleanXYZ.Property.Function
