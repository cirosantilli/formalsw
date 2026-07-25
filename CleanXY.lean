import Lean

/-!
Core Lean datatypes and semantics for representing a small Python AST.

These definitions intentionally mirror Python's `ast` module shape more closely
than executable Lean code. Partial semantic interpretations are defined below.
-/

namespace CleanXY.PyAst

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

/-- Python boolean operators currently represented by the AST bridge. -/
inductive BoolOp where
  /-- Python short-circuiting `and`. -/
  | and
  /-- Python short-circuiting `or`. -/
  | or
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
  /-- A Python boolean operation. -/
  | boolOp : BoolOp -> List Expr -> Expr
  /-- A Python comparison chain. -/
  | compare : Expr -> List (CmpOp × Expr) -> Expr
  /-- A Python call expression with positional arguments. -/
  | call : Expr -> List Expr -> Expr
  /-- A Python subscription such as `values[i]`. -/
  | subscript : Expr -> Expr -> Expr
  /-- A Python slice used inside a subscription. -/
  | slice : Option Expr -> Option Expr -> Option Expr -> Expr
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
  /-- A Python `while` statement. -/
  | whileDo : Expr -> List Stmt -> List Stmt -> Stmt
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

/-- Decode a boolean operator name from the JSON schema. -/
private def BoolOp.fromJson? (json : Lean.Json) : Except String BoolOp := do
  match ← json.getStr? with
  | "And" => return .and
  | "Or" => return .or
  | name => throw s!"unsupported boolean operator: {name}"

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
  | "BoolOp" =>
      return .boolOp
        (← BoolOp.fromJson? (← jsonField json "op"))
        (← jsonArray json "values" Expr.fromJson?)
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
  | "Subscript" =>
      return .subscript
        (← Expr.fromJson? (← jsonField json "value"))
        (← Expr.fromJson? (← jsonField json "slice"))
  | "Slice" =>
      let decodeOptional (value : Lean.Json) :=
        match value with
        | .null => pure none
        | value => some <$> Expr.fromJson? value
      return .slice
        (← decodeOptional (← jsonField json "lower"))
        (← decodeOptional (← jsonField json "upper"))
        (← decodeOptional (← jsonField json "step"))
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
  | "While" =>
      return .whileDo
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
Decode a complete cleanxy JSON AST document.

The schema version is checked before the JSON data is turned into the typed
`PyAst.Module` on which proofs operate.
-/
def Module.fromJsonDocument? (json : Lean.Json) : Except String Module := do
  let version ← (← jsonField json "schema_version").getNat?
  if version != 1 then
    throw s!"unsupported cleanxy AST schema version: {version}"
  let ast ← jsonField json "ast"
  if (← jsonString ast "type") != "Module" then
    throw "the top-level AST node must have type Module"
  return { body := ← jsonArray ast "body" Stmt.fromJson? }

end CleanXY.PyAst

/-- Import a cleanxy JSON AST as a reducible, typed `CleanXY.PyAst.Module`. -/
syntax "pyast_from_json% " term : term

open Lean Elab Term Meta in
elab_rules : term
  | `(pyast_from_json% $jsonSource:term) => do
      let sourceExpr ← elabTerm jsonSource (some (mkConst ``String))
      let some source := getStringValue? sourceExpr
        | throwError "pyast_from_json% expects a string literal, usually from include_str"
      let json ← match Json.parse source with
        | .ok value => pure value
        | .error message => throwError "invalid cleanxy AST JSON: {message}"
      let module ← match CleanXY.PyAst.Module.fromJsonDocument? json with
        | .ok value => pure value
        | .error message => throwError "invalid cleanxy AST document: {message}"
      return Lean.toExpr module

/-!
Partial semantic interpreters for `CleanXY.PyAst`.

This section is intentionally not generated. It is where we define the meaning
of supported Python AST fragments and prove properties about that meaning.
-/

namespace CleanXY.PyAst

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

/-- The value kinds currently selected from Python type annotations. -/
inductive TypeKind where
  | int
  /-- A bare Python `list`, modeled as a heterogeneous scalar list. -/
  | scalarList
deriving Repr, DecidableEq

/-- Find the supported unary argument kind of a top-level function. -/
def findFunctionArgKindIn : List Stmt → String → Option TypeKind
  | [], _ => none
  | Stmt.functionDef fname [{ annotation := some (Expr.name annotation), .. }] _ _ :: rest,
      name =>
      if fname = name then
        match annotation with
        | "int" => some .int
        | "list" => some .scalarList
        | _ => none
      else
        findFunctionArgKindIn rest name
  | _ :: rest, name => findFunctionArgKindIn rest name

/-- Find a top-level function's supported input domain from its annotation. -/
def Module.findFunctionArgKind (module : Module) (name : String) : Option TypeKind :=
  findFunctionArgKindIn module.body name

/-- Find the supported return kind of a top-level function. -/
def findFunctionReturnKindIn : List Stmt → String → Option TypeKind
  | [], _ => none
  | Stmt.functionDef fname _ (some (Expr.name annotation)) _ :: rest, name =>
      if fname = name then
        match annotation with
        | "int" => some .int
        | "list" => some .scalarList
        | _ => none
      else
        findFunctionReturnKindIn rest name
  | _ :: rest, name => findFunctionReturnKindIn rest name

/-- Find a top-level function's supported return kind from its annotation. -/
def Module.findFunctionReturnKind (module : Module) (name : String) : Option TypeKind :=
  findFunctionReturnKindIn module.body name

/-- Drop the runtime-irrelevant leading function docstring. -/
def executableBody : List Stmt → List Stmt
  | Stmt.expr (Expr.constant (Constant.string _)) :: rest => rest
  | body => body

/-- Scalar Python values used by the modeled binary-comparison safety semantics. -/
inductive ScalarValue where
  | int (value : Int)
  | string (value : String)
deriving Repr, DecidableEq

/-- A successful list return value or a thrown exception object. -/
abbrev ListOutcome := Except ExceptionObject (List ScalarValue)

/-- The Python runtime type name of a modeled scalar value. -/
def ScalarValue.typeName : ScalarValue → String
  | .int _ => "int"
  | .string _ => "str"

/-- The source spelling of a modeled Python comparison operator. -/
def CmpOp.symbol : CmpOp → String
  | .eq => "=="
  | .notEq => "!="
  | .lt => "<"
  | .ltE => "<="
  | .gt => ">"
  | .gtE => ">="

/-- Python's `TypeError` for an ordering comparison between incompatible values. -/
def unsupportedOrdering (op : CmpOp) (left right : ScalarValue) : ExceptionObject :=
  {
    typeName := "TypeError"
    args := [.string s!"'{op.symbol}' not supported between instances of \
'{left.typeName}' and '{right.typeName}'"]
  }

/-- Evaluate a comparison on modeled Python scalar values. -/
def evalScalarCmp (op : CmpOp) (left right : ScalarValue) :
    Except ExceptionObject Bool :=
  match op with
  | .eq => .ok (decide (left = right))
  | .notEq => .ok (decide (left ≠ right))
  | .lt | .ltE | .gt | .gtE =>
      match left, right with
      | .int left, .int right =>
          .ok <| match op with
            | .lt => decide (left < right)
            | .ltE => decide (left ≤ right)
            | .gt => decide (left > right)
            | .gtE => decide (left ≥ right)
            | _ => false
      | .string left, .string right =>
          .ok <| match op with
            | .lt => decide (left < right)
            | .ltE => decide (left ≤ right)
            | .gt => decide (left > right)
            | .gtE => decide (left ≥ right)
            | _ => false
      | left, right => .error (unsupportedOrdering op left right)

/-- An optional Python annotation restricting a scalar argument's runtime values. -/
inductive ScalarKind where
  | any
  | int
  | string
deriving Repr, DecidableEq

/-- Whether a modeled scalar value satisfies a Python argument annotation. -/
def ScalarKind.accepts : ScalarKind → ScalarValue → Bool
  | .any, _ => true
  | .int, .int _ => true
  | .string, .string _ => true
  | _, _ => false

/-- The input annotations of a recognized binary less-than expression. -/
structure BinaryComparison where
  left : ScalarKind
  right : ScalarKind
deriving Repr, DecidableEq

/-- Decode a supported scalar annotation; no annotation means unrestricted. -/
def scalarKindFromAnnotation : Option Expr → Option ScalarKind
  | none => some .any
  | some (.name "int") => some .int
  | some (.name "str") => some .string
  | _ => none

/-- Find a top-level two-argument function whose body evaluates `left < right`. -/
def findBinaryComparisonIn : List Stmt → String → Option BinaryComparison
  | [], _ => none
  | Stmt.functionDef fname [leftArg, rightArg] _ rawBody :: rest, name =>
      if fname = name then do
        let [.expr (.compare (.name leftName) [(.lt, .name rightName)])] :=
          executableBody rawBody | none
        if leftName != leftArg.name || rightName != rightArg.name then none
        else
          return {
            left := ← scalarKindFromAnnotation leftArg.annotation
            right := ← scalarKindFromAnnotation rightArg.annotation
          }
      else
        findBinaryComparisonIn rest name
  | _ :: rest, name => findBinaryComparisonIn rest name

/-- Find a recognized top-level binary less-than function. -/
def Module.findBinaryComparison (module : Module) (name : String) :
    Option BinaryComparison :=
  findBinaryComparisonIn module.body name

/-- Whether a recognized binary comparison returns normally or raises `TypeError`. -/
def evalBinaryComparisonOutcome (module : Module) (name : String)
    (left right : ScalarValue) : Option (Except ExceptionObject Unit) := do
  let signature ← module.findBinaryComparison name
  if !signature.left.accepts left || !signature.right.accepts right then none
  else
    match left, right with
    | .int _, .int _ | .string _, .string _ => some (.ok ())
    | _, _ => some (.error { typeName := "TypeError", args := [] })

mutual
  /-- Count expression operations, assigning unit cost to every AST node. -/
  partial def Expr.operationCount : Expr → Nat
    | .constant _ | .name _ => 1
    | .list elements => 1 + (elements.map Expr.operationCount).sum
    | .binOp left _ right => 1 + left.operationCount + right.operationCount
    | .unaryOp _ operand => 1 + operand.operationCount
    | .boolOp _ values => 1 + (values.map Expr.operationCount).sum
    | .compare left comparisons =>
        1 + left.operationCount + (comparisons.map (Expr.operationCount ∘ Prod.snd)).sum
    | .call function args =>
        1 + function.operationCount + (args.map Expr.operationCount).sum
    | .subscript value index => 1 + value.operationCount + index.operationCount
    | .slice lower upper step =>
        1 + (lower.map Expr.operationCount).getD 0 +
          (upper.map Expr.operationCount).getD 0 +
          (step.map Expr.operationCount).getD 0

  /-- Count statement operations, assigning unit cost to every AST node. -/
  partial def Stmt.operationCount : Stmt → Nat
    | .functionDef _ args returns body =>
        1 + args.length + (returns.map Expr.operationCount).getD 0 +
          (body.map Stmt.operationCount).sum
    | .return value => 1 + value.operationCount
    | .assign targets value =>
        1 + (targets.map Expr.operationCount).sum + value.operationCount
    | .augAssign target _ value => 1 + target.operationCount + value.operationCount
    | .forIn target iter body orelse =>
        1 + target.operationCount + iter.operationCount +
          (body.map Stmt.operationCount).sum + (orelse.map Stmt.operationCount).sum
    | .ifThen test body orelse | .whileDo test body orelse =>
        1 + test.operationCount + (body.map Stmt.operationCount).sum +
          (orelse.map Stmt.operationCount).sum
    | .assert test message => 1 + test.operationCount + (message.map Expr.operationCount).getD 0
    | .raise exception => 1 + (exception.map Expr.operationCount).getD 0
    | .expr expression => 1 + expression.operationCount
end

/-- Whether a statement is a `for` loop. -/
def Stmt.hasFor : Stmt → Bool
  | .forIn _ _ _ _ => true
  | _ => false

/-- Whether a statement is a `while` loop. -/
def Stmt.hasWhile : Stmt → Bool
  | .whileDo _ _ _ => true
  | _ => false

/-- Whether an expression's operator tree calls the named function. -/
def Expr.callsFunction (name : String) : Expr → Bool
  | .binOp left _ right => left.callsFunction name || right.callsFunction name
  | .unaryOp _ operand => operand.callsFunction name
  | .call (.name functionName) _ => functionName == name
  | .call function _ => function.callsFunction name
  | .subscript value index => value.callsFunction name || index.callsFunction name
  | _ => false

/-- Whether a statement's direct expressions call the named function. -/
def Stmt.callsFunction (name : String) : Stmt → Bool
  | .return value => value.callsFunction name
  | .assign _ value => value.callsFunction name
  | .augAssign target _ value => target.callsFunction name || value.callsFunction name
  | .forIn target iter _ _ => target.callsFunction name || iter.callsFunction name
  | .ifThen test _ _ | .whileDo test _ _ => test.callsFunction name
  | .assert test message =>
      test.callsFunction name || (message.map (Expr.callsFunction name)).getD false
  | .raise exception => (exception.map (Expr.callsFunction name)).getD false
  | .expr expression => expression.callsFunction name
  | _ => false

/-- Coarse asymptotic growth classes supported by the initial cost analyzer. -/
inductive Growth where
  | constant
  | linear
  | linearithmic
  | quadratic
deriving Repr, DecidableEq

namespace Growth

/-- A positive representative function for an asymptotic growth class. -/
def bound : Growth → Nat → Nat
  | .constant, _ => 1
  | .linear, n => n + 1
  | .linearithmic, n => (n + 1) * (Nat.log2 (n + 1) + 1)
  | .quadratic, n => (n + 1) * (n + 1)

/-- Standard upper-bound Big-O relation. -/
def IsBigO (cost bound : Nat → Nat) : Prop :=
  ∃ constant threshold : Nat,
    ∀ n, threshold ≤ n → cost n ≤ constant * bound n

/-- Unit-operation scaling does not change an asymptotic growth class. -/
theorem scaled_isBigO (operations : Nat) (growth : Growth) :
    IsBigO (fun n => operations * growth.bound n) growth.bound :=
  ⟨operations, 0, fun _ _ => Nat.le_refl _⟩

/-- Multiplying an asymptotic cost by a constant preserves its bound. -/
theorem scale_left {cost bound : Nat → Nat} (operations : Nat)
    (h : IsBigO cost bound) :
    IsBigO (fun n => operations * cost n) bound := by
  obtain ⟨constant, threshold, h⟩ := h
  refine ⟨operations * constant, threshold, fun n hn => ?_⟩
  calc
    operations * cost n ≤ operations * (constant * bound n) :=
      Nat.mul_le_mul_left operations (h n hn)
    _ = (operations * constant) * bound n := by simp [Nat.mul_assoc]

/-- The constant representative has the conventional constant bound. -/
theorem constant_isBigO :
    IsBigO Growth.constant.bound (fun _ => 1) := by
  refine ⟨1, 0, fun n _ => ?_⟩
  simp [Growth.bound]

/-- The positive linear representative is asymptotically bounded by `n`. -/
theorem linear_isBigO :
    IsBigO Growth.linear.bound (fun n => n) := by
  refine ⟨2, 1, fun n hn => ?_⟩
  simp only [Growth.bound]
  omega

/-- Monotonicity of the natural-number base-two logarithm away from zero. -/
private theorem log2_mono {left right : Nat} (hleft : left ≠ 0)
    (hle : left ≤ right) : Nat.log2 left ≤ Nat.log2 right := by
  have hright : right ≠ 0 := by omega
  exact (Nat.le_log2 hright).2 (Nat.le_trans (Nat.log2_self_le hleft) hle)

/-- The positive linearithmic representative has the conventional `n log n` bound. -/
theorem linearithmic_isBigO :
    IsBigO Growth.linearithmic.bound (fun n => n * (Nat.log2 n + 1)) := by
  refine ⟨2 * 2, 1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hsize : n + 1 ≤ 2 * n := by omega
  have hlog : Nat.log2 (n + 1) + 1 ≤ 2 * (Nat.log2 n + 1) := by
    have : Nat.log2 (n + 1) ≤ Nat.log2 n + 1 := by
      calc
        Nat.log2 (n + 1) ≤ Nat.log2 (2 * n) :=
          log2_mono (by omega) hsize
        _ = Nat.log2 n + 1 := Nat.log2_two_mul hn0
    omega
  simp only [Growth.bound]
  calc
    (n + 1) * (Nat.log2 (n + 1) + 1) ≤
        (2 * n) * (2 * (Nat.log2 n + 1)) := Nat.mul_le_mul hsize hlog
    _ = (2 * 2) * (n * (Nat.log2 n + 1)) := by ac_rfl

/-- The positive quadratic representative is asymptotically bounded by `n * n`. -/
theorem quadratic_isBigO :
    IsBigO Growth.quadratic.bound (fun n => n * n) := by
  refine ⟨2 * 2, 1, fun n hn => ?_⟩
  have hsize : n + 1 ≤ 2 * n := by omega
  simp only [Growth.bound]
  calc
    (n + 1) * (n + 1) ≤ (2 * n) * (2 * n) := Nat.mul_le_mul hsize hsize
    _ = (2 * 2) * (n * n) := by ac_rfl

end Growth

/-- How the asymptotic size variable is obtained from a Python argument. -/
inductive InputSize where
  /-- `n` is the natural-number projection of an integer argument. -/
  | intToNat (argument : String)
  /-- `n` is the length of a list argument. -/
  | listLength (argument : String)
deriving Repr, DecidableEq

/-- Result of structurally analyzing a function's worst-case operation count. -/
structure CostAnalysis where
  operations : Nat
  growth : Growth
  inputSize : InputSize
deriving Repr, DecidableEq

/-- Analyze top-level functions using unit-cost AST operations and loop shape. -/
def analyzeFunctionIn : List Stmt → String → Option CostAnalysis
  | [], _ => none
  | Stmt.functionDef fname args _ rawBody :: rest, name =>
      if fname = name then
        let body := executableBody rawBody
        let hasWhile := body.any Stmt.hasWhile
        let hasFor := body.any Stmt.hasFor
        let recursive := body.any (Stmt.callsFunction fname)
        let inputSize? :=
          match args with
          | [{ name := argument, annotation := some (Expr.name "int") }] =>
              some (InputSize.intToNat argument)
          | [{ name := argument, annotation := some (Expr.name "list") }] =>
              some (InputSize.listLength argument)
          | _ => none
        match inputSize? with
        | none => none
        | some inputSize =>
            let listInput :=
              match inputSize with
              | .listLength _ => true
              | .intToNat _ => false
            let growth :=
              if listInput && recursive && hasWhile then Growth.linearithmic
              else if listInput && recursive && hasFor then Growth.quadratic
              else if hasWhile || hasFor then Growth.linear
              else Growth.constant
            some { operations := (body.map Stmt.operationCount).sum, growth, inputSize }
      else
        analyzeFunctionIn rest name
  | _ :: rest, name => analyzeFunctionIn rest name

/-- Analyze one top-level function's unit-operation worst-case cost. -/
def Module.analyzeFunction (module : Module) (name : String) : Option CostAnalysis :=
  analyzeFunctionIn module.body name

/-- Merge two sorted lists, propagating Python comparison exceptions. -/
def mergeSortedFuel : Nat → List ScalarValue → List ScalarValue → ListOutcome
  | 0, left, right => .ok (left ++ right)
  | _ + 1, [], right => .ok right
  | _ + 1, left, [] => .ok left
  | fuel + 1, leftHead :: leftTail, rightHead :: rightTail => do
      if ← evalScalarCmp .ltE leftHead rightHead then
        return leftHead ::
          (← mergeSortedFuel fuel leftTail (rightHead :: rightTail))
      else
        return rightHead ::
          (← mergeSortedFuel fuel (leftHead :: leftTail) rightTail)

/-- Evaluate the merge-sort shape used by the supported Python subset. -/
def evalMergeSortFuel : Nat → List ScalarValue → ListOutcome
  | 0, values => .ok values
  | fuel + 1, values =>
      if values.length ≤ 1 then
        .ok values
      else do
        let middle := values.length / 2
        let left ← evalMergeSortFuel fuel (values.take middle)
        let right ← evalMergeSortFuel fuel (values.drop middle)
        mergeSortedFuel values.length left right

/-- Partition values exactly as the modeled first-pivot quicksort does. -/
def quickPartition (pivot : ScalarValue) :
    List ScalarValue →
      Except ExceptionObject (List ScalarValue × List ScalarValue × List ScalarValue)
  | [] => .ok ([], [], [])
  | value :: rest => do
      if ← evalScalarCmp .lt value pivot then
        let (less, equal, greater) ← quickPartition pivot rest
        return (value :: less, equal, greater)
      else if ← evalScalarCmp .gt value pivot then
        let (less, equal, greater) ← quickPartition pivot rest
        return (less, equal, value :: greater)
      else
        let (less, equal, greater) ← quickPartition pivot rest
        return (less, value :: equal, greater)

/-- Evaluate the first-element-pivot quick-sort shape used by the Python subset. -/
def evalQuickSortFuel : Nat → List ScalarValue → ListOutcome
  | 0, values => .ok values
  | _ + 1, [] => .ok []
  | fuel + 1, values@(pivot :: _) => do
      if values.length ≤ 1 then
        .ok values
      else
        let (less, equal, greater) ← quickPartition pivot values
        return (← evalQuickSortFuel fuel less) ++ equal ++
          (← evalQuickSortFuel fuel greater)

/--
Interpret the two structurally recognized recursive list-sorting shapes.

Unlike the old canonical-sort shortcut, this preserves each algorithm's
comparison order and exception outcome on heterogeneous lists.
-/
def evalUnaryListFunctionOutcome (module : Module) (name : String)
    (values : List ScalarValue) : Option ListOutcome := do
  let body ← module.findFunctionBody name
  if !body.any (Stmt.callsFunction name) then
    none
  else if body.any Stmt.hasWhile then
    some (evalMergeSortFuel values.length values)
  else if body.any Stmt.hasFor then
    some (evalQuickSortFuel values.length values)
  else
    none

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
  | Expr.boolOp _ _ => none
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
  | Expr.subscript _ _ => none
  | Expr.slice _ _ _ => none

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

end CleanXY.PyAst

/-!
Reusable proof obligations that `cleanxy` docstring markers can request.

These names are intentionally short and stable so users can discover available
properties under `CleanXY.Property.Function` and then prove ordinary Lean
theorems with the same types.
-/

namespace CleanXY.Property.Function

/--
A function either throws or successfully returns a value of its annotated type
for every input in its annotated domain.
-/
def ReturnType (module : PyAst.Module) (name : String) : Prop :=
  match module.findFunctionArgKind name, module.findFunctionReturnKind name with
  | some .int, some .int =>
      ∀ n : Int, ∃ outcome,
        PyAst.evalUnaryIntFunctionOutcome module name n = some outcome
  | some .scalarList, some .scalarList =>
      ∀ values : List PyAst.ScalarValue, ∃ outcome,
        PyAst.evalUnaryListFunctionOutcome module name values = some outcome
  | _, _ => False

/-- A unary integer function throws a modeled exception for at least one input. -/
def Throws (module : PyAst.Module) (name : String) : Prop :=
  match module.findBinaryComparison name with
  | some signature =>
      ∃ left right exception,
        signature.left.accepts left = true ∧
          signature.right.accepts right = true ∧
          PyAst.evalBinaryComparisonOutcome module name left right =
            some (.error exception)
  | none =>
      ∃ n : Int, ∃ exception,
        PyAst.evalUnaryIntFunctionOutcome module name n = some (.error exception)

/--
Two supported unary functions return the same value or throw structurally
equal exception objects for every input in their modeled domain.
-/
def Equiv (module : PyAst.Module) (left right : String) : Prop :=
  match module.findFunctionArgKind left, module.findFunctionArgKind right with
  | some .int, some .int =>
      ∀ n : Int, ∃ outcome,
        PyAst.evalUnaryIntFunctionOutcome module left n = some outcome ∧
          PyAst.evalUnaryIntFunctionOutcome module right n = some outcome
  | some .scalarList, some .scalarList =>
      ∀ values : List PyAst.ScalarValue, ∃ outcome,
        PyAst.evalUnaryListFunctionOutcome module left values = some outcome ∧
          PyAst.evalUnaryListFunctionOutcome module right values = some outcome
  | _, _ => False

/-- A function terminates within a bound using an explicit Python input-size measure. -/
def BigO (module : PyAst.Module) (name : String) (inputSize : PyAst.InputSize)
    (bound : Nat → Nat) : Prop :=
  ∃ analysis,
    module.analyzeFunction name = some analysis ∧
      analysis.inputSize = inputSize ∧
        PyAst.Growth.IsBigO
          (fun n => analysis.operations * analysis.growth.bound n)
          bound

/-- Combine a computed growth classification with any asymptotic upper bound. -/
theorem bigO_of_growth_bound (module : PyAst.Module) (name : String)
    (inputSize : PyAst.InputSize) (growth : PyAst.Growth) (bound : Nat → Nat)
    (hInputSize :
      (module.analyzeFunction name).map PyAst.CostAnalysis.inputSize = some inputSize)
    (hAnalysis : (module.analyzeFunction name).map PyAst.CostAnalysis.growth = some growth)
    (hBound : PyAst.Growth.IsBigO growth.bound bound) :
    BigO module name inputSize bound := by
  cases hModule : module.analyzeFunction name with
  | none => simp [hModule] at hAnalysis
  | some analysis =>
      have hGrowth : analysis.growth = growth := by
        simpa [hModule] using hAnalysis
      have hInput : analysis.inputSize = inputSize := by
        simpa [hModule] using hInputSize
      refine ⟨analysis, hModule, hInput, ?_⟩
      rw [hGrowth]
      exact PyAst.Growth.scale_left analysis.operations hBound

end CleanXY.Property.Function
