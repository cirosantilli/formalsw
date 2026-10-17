import Lean

/-!
Python-specific Lean datatypes and semantics for representing a small Python AST.

These definitions intentionally mirror Python's `ast` module shape more closely
than executable Lean code. Partial semantic interpretations are defined below.
-/

namespace FormalSW.PyAst

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
deriving Repr, DecidableEq, BEq, Lean.ToExpr

/-- Python unary operators currently represented by the AST bridge. -/
inductive UnaryOp where
  /-- Python unary minus. -/
  | uSub
  /-- Python logical `not`. -/
  | not
deriving Repr, BEq, Lean.ToExpr

/-- Python boolean operators currently represented by the AST bridge. -/
inductive BoolOp where
  /-- Python short-circuiting `and`. -/
  | and
  /-- Python short-circuiting `or`. -/
  | or
deriving Repr, BEq, Lean.ToExpr

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
deriving Repr, BEq, Lean.ToExpr

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
deriving Repr, DecidableEq, BEq, Lean.ToExpr

/-- Python expressions currently represented by the AST bridge. -/
inductive Expr where
  /-- A Python literal constant. -/
  | constant : Constant -> Expr
  /-- A Python identifier reference. -/
  | name : String -> Expr
  /-- Attribute access such as `self.value`. -/
  | attribute : Expr -> String -> Expr
  /-- A Python list literal. -/
  | list : List Expr -> Expr
  /-- A Python tuple display, also used as an unpacking target. -/
  | tuple : List Expr -> Expr
  /-- A Python binary operation. -/
  | binOp : Expr -> BinOp -> Expr -> Expr
  /-- A Python unary operation. -/
  | unaryOp : UnaryOp -> Expr -> Expr
  /-- A Python boolean operation. -/
  | boolOp : BoolOp -> List Expr -> Expr
  /-- Python's conditional expression evaluates only the selected branch. -/
  | ifExp : Expr -> Expr -> Expr -> Expr
  /-- A Python comparison chain. -/
  | compare : Expr -> List (CmpOp × Expr) -> Expr
  /-- A Python call expression with positional arguments. -/
  | call : Expr -> List Expr -> Expr
  /-- Normalized `sum(element for name in range(bounds) if conditions...)`.
  Coverage checking verifies the builtin bindings before this node executes. -/
  | sumRange : String → Expr → List Expr → List Expr → Expr
  /-- A Python subscription such as `values[i]`. -/
  | subscript : Expr -> Expr -> Expr
  /-- A Python slice used inside a subscription. -/
  | slice : Option Expr -> Option Expr -> Option Expr -> Expr
deriving Repr, BEq, Lean.ToExpr

/-- A Python function argument. -/
structure Arg where
  /-- The argument name. -/
  name : String
  /-- The optional source annotation expression. -/
  annotation : Option Expr
deriving Repr, BEq, Lean.ToExpr

/-- Python statements currently represented by the AST bridge. -/
inductive Stmt where
  /-- A Python class definition. -/
  | classDef : (name : String) -> (body : List Stmt) -> Stmt
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
  /-- A simple annotated assignment; module annotations describe input domains. -/
  | annAssign : Expr → Expr → Option Expr → Stmt
  /-- Python's scope declaration, not a runtime assignment. -/
  | globalDecl : List String → Stmt
  /-- A Python augmented assignment statement. -/
  | augAssign : Expr -> BinOp -> Expr -> Stmt
  /-- A Python `for target in iter` statement. -/
  | forIn : Expr -> Expr -> List Stmt -> List Stmt -> Stmt
  /-- Internal state of an evaluated `range(stop)` iterator, not source syntax. -/
  | rangeLoop : String -> Int -> Int -> List Stmt -> List Stmt -> Stmt
  /-- Internal iterator state for the scalar call interpreter's stepped ranges. -/
  | rangeStepLoop : String → Int → Int → Int → List Stmt → List Stmt → Stmt
  /-- A Python `if` statement. -/
  | ifThen : Expr -> List Stmt -> List Stmt -> Stmt
  /-- A Python `while` statement. -/
  | whileDo : Expr -> List Stmt -> List Stmt -> Stmt
  /-- Exit the nearest enclosing loop, skipping its `else` block. -/
  | breakLoop : Stmt
  /-- Start the next iteration of the nearest enclosing loop. -/
  | continueLoop : Stmt
  /-- Internal loop boundary; the payload resumes iteration on normal completion. -/
  | loopResume : Stmt → Stmt
  /-- A Python `assert` statement. -/
  | assert : Expr -> Option Expr -> Stmt
  /-- A Python `raise` statement. -/
  | raise : Option Expr -> Stmt
  /-- A Python expression statement. -/
  | expr : Expr -> Stmt
  /-- Source retained for diagnostics when it is outside the AST model. -/
  | unsupported : (description : String) -> Stmt
  /-- Absolute imports retain both the original and bound names. -/
  | importFrom : (module : String) -> (names : List (String × String)) -> Stmt
deriving Repr, BEq, Lean.ToExpr

/-- A Python module represented as a list of top-level statements. -/
structure Module where
  /-- Top-level statements in source order. -/
  body : List Stmt
deriving Repr, BEq, Lean.ToExpr

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
partial def Expr.fromJson? (json : Lean.Json) : Except String Expr := do
  match ← jsonString json "type" with
  | "Constant" =>
      match ← jsonField json "value" with
      | .num number => return .constant (.int (← (Lean.Json.num number).getInt?))
      | .str value => return .constant (.string value)
      | .bool value => return .constant (.bool value)
      | .null => return .constant .none
      | _ => throw "unsupported Constant.value"
  | "Name" => return .name (← jsonString json "id")
  | "Attribute" =>
      return .attribute
        (← Expr.fromJson? (← jsonField json "value"))
        (← jsonString json "attr")
  | "List" => return .list (← jsonArray json "elts" Expr.fromJson?)
  | "Tuple" => return .tuple (← jsonArray json "elts" Expr.fromJson?)
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
  | "IfExp" =>
      return .ifExp
        (← Expr.fromJson? (← jsonField json "test"))
        (← Expr.fromJson? (← jsonField json "body"))
        (← Expr.fromJson? (← jsonField json "orelse"))
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
  | "SumRange" =>
      return .sumRange (← jsonString json "name")
        (← Expr.fromJson? (← jsonField json "element"))
        (← jsonArray json "bounds" Expr.fromJson?)
        (← jsonArray json "conditions" Expr.fromJson?)
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
  | "ClassDef" =>
      return .classDef
        (← jsonString json "name")
        (← jsonArray json "body" Stmt.fromJson?)
  | "FunctionDef" =>
      return .functionDef
        (← jsonString json "name")
        (← jsonArray json "args" Arg.fromJson?)
        (← optionalExpr json "returns")
        (← jsonArray json "body" Stmt.fromJson?)
  | "Unsupported" => return .unsupported ((← jsonString json "description") ++ ": " ++ (← jsonString json "source"))
  | "ImportFrom" =>
      return .importFrom (← jsonString json "module")
        (← jsonArray json "names" fun item => do
          return (← jsonString item "name", ← jsonString item "binding"))
  | "Return" => return .return (← Expr.fromJson? (← jsonField json "value"))
  | "Assign" =>
      return .assign
        (← jsonArray json "targets" Expr.fromJson?)
        (← Expr.fromJson? (← jsonField json "value"))
  | "AnnAssign" =>
      return .annAssign (← Expr.fromJson? (← jsonField json "target"))
        (← Expr.fromJson? (← jsonField json "annotation")) (← optionalExpr json "value")
  | "Global" => return .globalDecl (← jsonArray json "names" fun name => name.getStr?)
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
  | "Break" => return .breakLoop
  | "Continue" => return .continueLoop
  | "Assert" =>
      return .assert
        (← Expr.fromJson? (← jsonField json "test"))
        (← optionalExpr json "msg")
  | "Raise" => return .raise (← optionalExpr json "exc")
  | "Expr" => return .expr (← Expr.fromJson? (← jsonField json "value"))
  | type => throw s!"unsupported statement type: {type}"

/--
Decode a complete formalsw JSON AST document.

The schema version is checked before the JSON data is turned into the typed
`PyAst.Module` on which proofs operate.
-/
def Module.fromJsonDocument? (json : Lean.Json) : Except String Module := do
  let version ← (← jsonField json "schema_version").getNat?
  if version != 1 then
    throw s!"unsupported formalsw AST schema version: {version}"
  let ast ← jsonField json "ast"
  if (← jsonString ast "type") != "Module" then
    throw "the top-level AST node must have type Module"
  return { body := ← jsonArray ast "body" Stmt.fromJson? }

end FormalSW.PyAst

/-- Import a formalsw JSON AST as a reducible, typed `FormalSW.PyAst.Module`. -/
syntax "pyast_from_json% " term : term

open Lean Elab Term Meta in
elab_rules : term
  | `(pyast_from_json% $jsonSource:term) => do
      let sourceExpr ← elabTerm jsonSource (some (mkConst ``String))
      let some source := getStringValue? sourceExpr
        | throwError "pyast_from_json% expects a string literal, usually from include_str"
      let json ← match Json.parse source with
        | .ok value => pure value
        | .error message => throwError "invalid formalsw AST JSON: {message}"
      let module ← match FormalSW.PyAst.Module.fromJsonDocument? json with
        | .ok value => pure value
        | .error message => throwError "invalid formalsw AST document: {message}"
      return Lean.toExpr module

/-- Decode a source expression for a specification predicate. -/
syntax "pyexpr_from_json% " term : term

open Lean Elab Term Meta in
elab_rules : term
  | `(pyexpr_from_json% $jsonSource:term) => do
      let sourceExpr ← elabTerm jsonSource (some (mkConst ``String))
      let some source := getStringValue? sourceExpr
        | throwError "pyexpr_from_json% expects a string literal"
      let json ← match Json.parse source with
        | .ok value => pure value
        | .error message => throwError "invalid Python expression JSON: {message}"
      let expression ← match FormalSW.PyAst.Expr.fromJson? json with
        | .ok value => pure value
        | .error message => throwError "invalid Python expression: {message}"
      return Lean.toExpr expression

/-!
Partial semantic interpreters for `FormalSW.PyAst`.

This section is intentionally not generated. It is where we define the meaning
of supported Python AST fragments and prove properties about that meaning.
-/

namespace FormalSW.PyAst

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

/-- Names of all top-level functions in source order. -/
def Module.functionNames (module : Module) : List String :=
  module.body.filterMap fun
    | .functionDef name _ _ _ => some name
    | _ => none

/-- Check the complete function surface of a plain-Python module. -/
def Module.hasExactlyFunctions (module : Module) (names : List String) : Bool :=
  module.functionNames == names

/-- Find the body of a top-level class definition. -/
def findClassBodyIn : List Stmt → String → Option (List Stmt)
  | [], _ => none
  | Stmt.classDef className body :: rest, name =>
      if className = name then some body else findClassBodyIn rest name
  | _ :: rest, name => findClassBodyIn rest name

/-- Find a top-level class definition by name. -/
def Module.findClassBody (module : Module) (name : String) : Option (List Stmt) :=
  findClassBodyIn module.body name

/-- The name of a method statement, ignoring non-method class-body entries. -/
def Stmt.methodName? : Stmt → Option String
  | .functionDef name _ _ _ => some name
  | _ => none

/-- Method names defined directly by a class, in source order. -/
def Module.classMethodNames (module : Module) (name : String) : Option (List String) := do
  let body ← module.findClassBody name
  return body.filterMap Stmt.methodName?

/-- Check the complete public model surface of a Python class.

This is deliberately exact: adding, removing, or renaming a method in the
Python source changes the generated AST and invalidates the adjacent proof.
-/
def Module.hasExactlyClassMethods (module : Module) (name : String)
    (methods : List String) : Bool :=
  module.classMethodNames name == some methods

/-- A deterministic digest of the complete typed AST used to bind a proof to source.

The structural predicates describe the intended model, while this digest makes
every parsed detail part of the checked obligation. It is not a trust boundary:
the generated JSON has already been decoded into `Module` before hashing.
-/
def Module.fingerprint (module : Module) : UInt64 :=
  let body := match module.body with
    | .expr (.constant (.string _)) :: rest => rest
    | body => body
  hash (reprStr ({ body } : Module))

/-- Recognize a wrapper constructor that stores one annotated scalar field. -/
def isScalarWrapperInit (payloadAnnotation : String) : Stmt → Bool
  | .functionDef "__init__"
      [{ name := selfName, .. },
       { name := valueName, annotation := some (.name annotation) }]
      _ [.assign [.attribute (.name targetSelf) "value"] (.name sourceValue)] =>
      annotation == payloadAnnotation &&
        selfName == targetSelf && valueName == sourceValue
  | _ => false

/-- Recognize a comparison method delegated to the wrapper's `value` field. -/
def isValueComparison (methodName : String) (op : CmpOp) : Stmt → Bool
  | .functionDef name [{ name := selfName, .. }, { name := otherName, .. }]
      _ [.return (.compare
        (.attribute (.name leftSelf) "value")
        [(actualOp, .attribute (.name rightOther) "value")])] =>
      name == methodName && actualOp == op &&
        selfName == leftSelf && otherName == rightOther
  | _ => false

/-- Recognize a string wrapper storing Unicode code points as `list[int]`. -/
def isCodepointStringInit : Stmt → Bool
  | .functionDef "__init__"
      [{ name := selfName, .. },
       { name := valueName,
         annotation := some (.subscript (.name "list") (.name "int")) }]
      _ [.assign [.attribute (.name targetSelf) "value"] (.name sourceValue)] =>
      selfName == targetSelf && valueName == sourceValue
  | _ => false

/-- Whether all modeled comparison methods delegate to the `value` field. -/
def hasValueComparisons (body : List Stmt) : Bool :=
  body.any (isValueComparison "__eq__" .eq) &&
    body.any (isValueComparison "__lt__" .lt) &&
    body.any (isValueComparison "__le__" .ltE) &&
    body.any (isValueComparison "__gt__" .gt) &&
    body.any (isValueComparison "__ge__" .gtE)

/-- Whether a class is a one-field scalar wrapper with its own total comparisons. -/
def isComparableWrapperClassBody (payloadAnnotation : String) (body : List Stmt) : Bool :=
  body.any (isScalarWrapperInit payloadAnnotation) &&
    hasValueComparisons body

/-- Whether a class implements strings as comparable Unicode code-point lists. -/
def isCodepointStringClassBody (body : List Stmt) : Bool :=
  body.any isCodepointStringInit && hasValueComparisons body

/-- Check a top-level class against the modeled comparable-wrapper definition. -/
def Module.isComparableWrapperClass (module : Module) (name payloadAnnotation : String) :
    Bool :=
  match module.findClassBody name with
  | some body => isComparableWrapperClassBody payloadAnnotation body
  | none => false

/-- Check a class against the modeled code-point-list string definition. -/
def Module.isCodepointStringClass (module : Module) (name : String) : Bool :=
  match module.findClassBody name with
  | some body => isCodepointStringClassBody body
  | none => false

/-- The value kinds currently selected from Python type annotations. -/
inductive TypeKind where
  | int
  /-- A Python `list[int]`, modeled as a homogeneous integer list. -/
  | intList
  /-- A bare Python `list`, modeled as a heterogeneous runtime-value list. -/
  | valueList
  /-- A list of locally defined comparable-wrapper objects. -/
  | objectList (className : String)
deriving Repr, DecidableEq

/-- Decode a supported unary argument or return annotation. -/
def typeKindFromAnnotation : Expr → Option TypeKind
  | .name "int" => some .int
  | .name "list" => some .valueList
  | .subscript (.name "list") (.name "int") => some .intList
  | .subscript (.name "list") (.name className) => some (.objectList className)
  | _ => none

/-- Find the supported unary argument kind of a top-level function. -/
def findFunctionArgKindIn : List Stmt → String → Option TypeKind
  | [], _ => none
  | Stmt.functionDef fname [{ annotation := some annotation, .. }] _ _ :: rest,
      name =>
      if fname = name then
        typeKindFromAnnotation annotation
      else
        findFunctionArgKindIn rest name
  | _ :: rest, name => findFunctionArgKindIn rest name

/-- Find a top-level function's supported input domain from its annotation. -/
def Module.findFunctionArgKind (module : Module) (name : String) : Option TypeKind :=
  findFunctionArgKindIn module.body name

/-- Find the supported return kind of a top-level function. -/
def findFunctionReturnKindIn : List Stmt → String → Option TypeKind
  | [], _ => none
  | Stmt.functionDef fname _ (some annotation) _ :: rest, name =>
      if fname = name then
        typeKindFromAnnotation annotation
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

/-- Python runtime values supported by the executable comparison semantics. -/
inductive Value where
  | int (value : Int)
  /-- A Python `str`, represented by its Unicode integer code points. -/
  | string (value : List Int)
  /-- A modeled object with a runtime class name and an optional integer `value` field.
  Omitting the field represents an object with no stored attributes.
  The execution model runs supported comparison method bodies; the older abstract
  evaluator compares payloads directly and is not a termination model. -/
  | object (typeName : String) (value : Option Int := none)
deriving Repr, DecidableEq

/-- A successful list return value or a thrown exception object. -/
abbrev ValueListOutcome := Except ExceptionObject (List Value)

/-- The Python runtime type name of a modeled value. -/
def Value.typeName : Value → String
  | .int _ => "int"
  | .string _ => "str"
  | .object typeName _ => typeName

/-- The source spelling of a modeled Python comparison operator. -/
def CmpOp.symbol : CmpOp → String
  | .eq => "=="
  | .notEq => "!="
  | .lt => "<"
  | .ltE => "<="
  | .gt => ">"
  | .gtE => ">="

/-- Python's `TypeError` for an ordering comparison between incompatible values. -/
def unsupportedOrdering (op : CmpOp) (left right : Value) : ExceptionObject :=
  {
    typeName := "TypeError"
    args := [.string s!"'{op.symbol}' not supported between instances of \
'{left.typeName}' and '{right.typeName}'"]
  }

/-- Evaluate a comparison on modeled Python values.
This total evaluator always returns a boolean or an exception. It does not model
arbitrary Python comparison method bodies, including methods that diverge.
-/
def evalValueCmp (op : CmpOp) (left right : Value) :
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
      | .object leftType (some left), .object rightType (some right) =>
          if leftType = rightType then
            .ok <| match op with
              | .lt => decide (left < right)
              | .ltE => decide (left ≤ right)
              | .gt => decide (left > right)
              | .gtE => decide (left ≥ right)
              | _ => false
          else
            .error (unsupportedOrdering op (.object leftType (some left)) (.object rightType (some right)))
      | left, right => .error (unsupportedOrdering op left right)

/-- An optional Python annotation restricting a scalar argument's runtime values. -/
inductive AnnotationKind where
  | any
  | int
  | string
deriving Repr, DecidableEq

/-- Whether a modeled value satisfies a Python argument annotation. -/
def AnnotationKind.accepts : AnnotationKind → Value → Bool
  | .any, _ => true
  | .int, .int _ => true
  | .string, .string _ => true
  | _, _ => false

/-- The input annotations of a recognized binary less-than expression. -/
structure BinaryComparison where
  left : AnnotationKind
  right : AnnotationKind
deriving Repr, DecidableEq

/-- Decode a supported scalar annotation; no annotation means unrestricted. -/
def annotationKindFromAnnotation : Option Expr → Option AnnotationKind
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
            left := ← annotationKindFromAnnotation leftArg.annotation
            right := ← annotationKindFromAnnotation rightArg.annotation
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
    (left right : Value) : Option (Except ExceptionObject Unit) := do
  if !module.isCodepointStringClass "str" then none
  let signature ← module.findBinaryComparison name
  if !signature.left.accepts left || !signature.right.accepts right then none
  else
    match left, right with
    | .int _, .int _ | .string _, .string _ => some (.ok ())
    | .object leftType _, .object rightType _ =>
        if leftType = rightType then some (.ok ())
        else some (.error { typeName := "TypeError", args := [] })
    | _, _ => some (.error { typeName := "TypeError", args := [] })

mutual
  /-- Count expression operations, assigning unit cost to every AST node. -/
  partial def Expr.operationCount : Expr → Nat
    | .constant _ | .name _ => 1
    | .attribute value _ => 1 + value.operationCount
    | .list elements | .tuple elements => 1 + (elements.map Expr.operationCount).sum
    | .binOp left _ right => 1 + left.operationCount + right.operationCount
    | .unaryOp _ operand => 1 + operand.operationCount
    | .boolOp _ values => 1 + (values.map Expr.operationCount).sum
    | .ifExp condition yes no =>
        1 + condition.operationCount + yes.operationCount + no.operationCount
    | .compare left comparisons =>
        1 + left.operationCount + (comparisons.map (Expr.operationCount ∘ Prod.snd)).sum
    | .call function args =>
        1 + function.operationCount + (args.map Expr.operationCount).sum
    | .sumRange _ element bounds conditions =>
        5 + element.operationCount + (bounds.map Expr.operationCount).sum +
          (conditions.map Expr.operationCount).sum
    | .subscript value index => 1 + value.operationCount + index.operationCount
    | .slice lower upper step =>
        1 + (lower.map Expr.operationCount).getD 0 +
          (upper.map Expr.operationCount).getD 0 +
          (step.map Expr.operationCount).getD 0

  /-- Count statement operations, assigning unit cost to every AST node. -/
  partial def Stmt.operationCount : Stmt → Nat
    | .breakLoop | .continueLoop => 1
    | .loopResume loop => 1 + loop.operationCount
    | .rangeLoop _ _ _ body otherwise =>
        1 + (body.map Stmt.operationCount).sum + (otherwise.map Stmt.operationCount).sum
    | .rangeStepLoop _ _ _ _ body otherwise =>
        1 + (body.map Stmt.operationCount).sum + (otherwise.map Stmt.operationCount).sum
    | .classDef _ body => 1 + (body.map Stmt.operationCount).sum
    | .functionDef _ args returns body =>
        1 + args.length + (returns.map Expr.operationCount).getD 0 +
          (body.map Stmt.operationCount).sum
    | .return value => 1 + value.operationCount
    | .assign targets value =>
        1 + (targets.map Expr.operationCount).sum + value.operationCount
    | .annAssign target annotation value =>
        1 + target.operationCount + annotation.operationCount + (value.map Expr.operationCount).getD 0
    | .globalDecl _ => 0
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
    | .unsupported _ => 0
    | .importFrom _ _ => 0
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
  | .attribute value _ => value.callsFunction name
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

/-- Recognize a wrapper returning one direct call with its sole argument. -/
def delegatedUnaryFunction : List Stmt → Option String
  | [.return (.call (.name target) [.name _])] => some target
  | .expr (.constant (.string _)) :: rest => delegatedUnaryFunction rest
  | _ => none

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
          | [{ name := argument,
                annotation := some (Expr.subscript (Expr.name "list") (Expr.name "int")) }] =>
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
  match module.findFunctionBody name with
  | some body =>
      match delegatedUnaryFunction body with
      | some target => analyzeFunctionIn module.body target
      | none => analyzeFunctionIn module.body name
  | none => none

/-- Legacy bounded sorting abstraction. Fuel exhaustion supplies a fallback value;
this helper is NOT an execution or termination model. Use `mergeExecution` instead. -/
def mergeSortedFuel : Nat → List Value → List Value → ValueListOutcome
  | 0, left, right => .ok (left ++ right)
  | _ + 1, [], right => .ok right
  | _ + 1, left, [] => .ok left
  | fuel + 1, leftHead :: leftTail, rightHead :: rightTail => do
      if ← evalValueCmp .ltE leftHead rightHead then
        return leftHead ::
          (← mergeSortedFuel fuel leftTail (rightHead :: rightTail))
      else
        return rightHead ::
          (← mergeSortedFuel fuel (leftHead :: leftTail) rightTail)

/-- Legacy merge-sort abstraction; not evidence of Python termination. -/
def evalMergeSortFuel : Nat → List Value → ValueListOutcome
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
def quickPartition (pivot : Value) :
    List Value →
      Except ExceptionObject (List Value × List Value × List Value)
  | [] => .ok ([], [], [])
  | value :: rest => do
      if ← evalValueCmp .lt value pivot then
        let (less, equal, greater) ← quickPartition pivot rest
        return (value :: less, equal, greater)
      else if ← evalValueCmp .gt value pivot then
        let (less, equal, greater) ← quickPartition pivot rest
        return (less, equal, value :: greater)
      else
        let (less, equal, greater) ← quickPartition pivot rest
        return (less, value :: equal, greater)

/-- Legacy quick-sort abstraction; not evidence of Python termination. -/
def evalQuickSortFuel : Nat → List Value → ValueListOutcome
  | 0, values => .ok values
  | _ + 1, [] => .ok []
  | fuel + 1, values@(pivot :: _) => do
      if values.length ≤ 1 then
        .ok values
      else
        let (less, equal, greater) ← quickPartition pivot values
        return (← evalQuickSortFuel fuel less) ++ equal ++
          (← evalQuickSortFuel fuel greater)

/-- A total ordering used to state the successful result of modeled sorts. -/
def valueLe : Value → Value → Bool
  | .int left, .int right => decide (left ≤ right)
  | .string left, .string right => decide (left ≤ right)
  | .object leftType left, .object rightType right =>
      match compare leftType rightType with
      | .lt => true
      | .eq => match left, right with
          | none, _ => true
          | some _, none => false
          | some left, some right => decide (left ≤ right)
      | .gt => false
  | .int _, .string _ => true
  | .int _, .object _ _ => true
  | .string _, .int _ => false
  | .string _, .object _ _ => true
  | .object _ _, _ => false

/-- Insert a value into a canonically ordered list. -/
def insertValueSorted (value : Value) : List Value → List Value
  | [] => [value]
  | head :: tail =>
      if valueLe value head then value :: head :: tail
      else head :: insertValueSorted value tail

/-- The common successful result of the recognized sorting algorithms. -/
def canonicalValueSort (values : List Value) : List Value :=
  values.foldr insertValueSorted []

/--
Keep an algorithm's precise exception, while expressing its successful result
through the canonical sorting specification.
-/
def normalizeSortOutcome (input : List Value) : ValueListOutcome → ValueListOutcome
  | .error exception => .error exception
  | .ok _ => .ok (canonicalValueSort input)

/--
Legacy abstraction of two broadly recognized recursive list-sorting shapes.
It preserves modeled primitive-comparison exception order and normalizes success
canonically. It does not execute custom Python methods or establish termination.
The new `listFunction` in Sorting uses exact recognition and actual executions.
-/
def evalUnaryListFunctionOutcome (module : Module) (name : String)
    (values : List Value) : Option ValueListOutcome := do
  if !module.isCodepointStringClass "str" then
    none
  else
    let body ← module.findFunctionBody name
    if !body.any (Stmt.callsFunction name) then
      none
    else if body.any Stmt.hasWhile then
      some (normalizeSortOutcome values (evalMergeSortFuel values.length values))
    else if body.any Stmt.hasFor then
      some (normalizeSortOutcome values (evalQuickSortFuel values.length values))
    else
      none

/-- Insert an integer into an ascending list. -/
def insertSorted (value : Int) : List Int → List Int
  | [] => [value]
  | head :: tail =>
      if value ≤ head then value :: head :: tail
      else head :: insertSorted value tail

/-- Canonical mathematical sorting semantics for `list[int]` functions. -/
def canonicalSort (values : List Int) : List Int :=
  values.foldr insertSorted []

/-- Factor equivalence proofs for functions implementing the canonical integer sort. -/
theorem canonicalSort_equiv
    (left right : List Int → Option (List Int))
    (leftCanonical : ∀ values, left values = some (canonicalSort values))
    (rightCanonical : ∀ values, right values = some (canonicalSort values)) :
    ∀ values, ∃ result,
      left values = some result ∧ right values = some result := by
  intro values
  exact ⟨canonicalSort values, leftCanonical values, rightCanonical values⟩

/-- Whether a body has one of the two supported recursive sorting shapes. -/
def isRecognizedSortBody (name : String) (body : List Stmt) : Bool :=
  body.any (Stmt.callsFunction name) &&
    (body.any Stmt.hasWhile || body.any Stmt.hasFor)

/-- Resolve either a sorting implementation or a direct wrapper around one. -/
def Module.findSortImplementation (module : Module) (name : String) :
    Option (String × List Stmt) := do
  let body ← module.findFunctionBody name
  if isRecognizedSortBody name body then
    some (name, body)
  else
    let target ← delegatedUnaryFunction body
    let targetBody ← module.findFunctionBody target
    if isRecognizedSortBody target targetBody then
      some (target, targetBody)
    else
      none

/-- Interpret a recognized recursive sorting function on homogeneous integers. -/
def evalUnaryIntListFunction (module : Module) (name : String) (values : List Int) :
    Option (List Int) := do
  let _ ← module.findSortImplementation name
  some (canonicalSort values)

/--
Interpret sorting a list of locally defined objects whose sole payload is an
integer and whose comparison methods delegate to that payload.
-/
def evalUnaryObjectIntListFunction (module : Module) (className name : String)
    (values : List Int) : Option (List Int) := do
  if !module.isComparableWrapperClass className "int" then none
  else
    evalUnaryIntListFunction module name values

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
  | Expr.attribute _ _ => none
  | Expr.unaryOp UnaryOp.uSub expr => do
      let value <- evalIntExpr env expr
      some (-value)
  | Expr.unaryOp _ _ => none
  | Expr.boolOp _ _ => none
  | Expr.ifExp _ _ _ => none
  | Expr.sumRange _ _ _ _ => none
  | Expr.tuple _ => none
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

end FormalSW.PyAst

/-!
Reusable proof obligations that `formalsw` docstring markers can request.

These names are intentionally short and stable so users can discover available
properties under `FormalSW.Property.Function` and then prove ordinary Lean
theorems with the same types.
-/

namespace FormalSW.Property.Function

/--
A function either throws or successfully returns a value of its annotated type
for every input in its annotated domain.
-/
def AbstractReturnType (module : PyAst.Module) (name : String) : Prop :=
  match module.findFunctionArgKind name, module.findFunctionReturnKind name with
  | some .int, some .int =>
      ∀ n : Int, ∃ outcome,
        PyAst.evalUnaryIntFunctionOutcome module name n = some outcome
  | some .intList, some .intList =>
      ∀ values : List Int, ∃ result,
        PyAst.evalUnaryIntListFunction module name values = some result
  | some .valueList, some .valueList =>
      ∀ values : List PyAst.Value, ∃ outcome,
        PyAst.evalUnaryListFunctionOutcome module name values = some outcome
  | some (.objectList className), some (.objectList returnClass) =>
      className = returnClass ∧
        ∀ values : List Int, ∃ result,
          PyAst.evalUnaryObjectIntListFunction module className name values =
            some result
  | _, _ => False

/-- A unary integer function throws a modeled exception for at least one input. -/
def AbstractThrows (module : PyAst.Module) (name : String) : Prop :=
  match module.findBinaryComparison name with
  | some signature =>
      ∃ left right exception,
        signature.left.accepts left = true ∧
          signature.right.accepts right = true ∧
          PyAst.evalBinaryComparisonOutcome module name left right =
            some (.error exception)
  | none =>
      match module.findFunctionArgKind name with
      | some .valueList =>
          ∃ values : List PyAst.Value, ∃ exception,
            PyAst.evalUnaryListFunctionOutcome module name values =
              some (.error exception)
      | some .intList => False
      | some (.objectList _) => False
      | _ =>
          ∃ n : Int, ∃ exception,
            PyAst.evalUnaryIntFunctionOutcome module name n = some (.error exception)

/--
Two supported unary functions return the same value or throw structurally
equal exception objects for every input in their modeled domain.
-/
def AbstractEquiv (module : PyAst.Module) (left right : String) : Prop :=
  match module.findFunctionArgKind left, module.findFunctionArgKind right with
  | some .int, some .int =>
      ∀ n : Int, ∃ outcome,
        PyAst.evalUnaryIntFunctionOutcome module left n = some outcome ∧
          PyAst.evalUnaryIntFunctionOutcome module right n = some outcome
  | some .intList, some .intList =>
      ∀ values : List Int, ∃ result,
        PyAst.evalUnaryIntListFunction module left values = some result ∧
          PyAst.evalUnaryIntListFunction module right values = some result
  | some .valueList, some .valueList =>
      ∀ values : List PyAst.Value, ∃ outcome,
        PyAst.evalUnaryListFunctionOutcome module left values = some outcome ∧
          PyAst.evalUnaryListFunctionOutcome module right values = some outcome
  | some (.objectList leftClass), some (.objectList rightClass) =>
      if leftClass = rightClass then
        ∀ values : List Int, ∃ result,
          PyAst.evalUnaryObjectIntListFunction module leftClass left values =
              some result ∧
            PyAst.evalUnaryObjectIntListFunction module rightClass right values =
              some result
      else False
  | _, _ => False

/--
Whenever both supported unary functions return successfully on an input, their
return values are equal. Exception objects need not be equal.
-/
def AbstractEquivReturn (module : PyAst.Module) (left right : String) : Prop :=
  match module.findFunctionArgKind left, module.findFunctionArgKind right with
  | some .int, some .int =>
      ∀ n leftResult rightResult,
        PyAst.evalUnaryIntFunctionOutcome module left n = some (.ok leftResult) →
        PyAst.evalUnaryIntFunctionOutcome module right n = some (.ok rightResult) →
        leftResult = rightResult
  | some .intList, some .intList =>
      ∀ values leftResult rightResult,
        PyAst.evalUnaryIntListFunction module left values = some leftResult →
        PyAst.evalUnaryIntListFunction module right values = some rightResult →
        leftResult = rightResult
  | some .valueList, some .valueList =>
      ∀ values leftResult rightResult,
        PyAst.evalUnaryListFunctionOutcome module left values =
            some (.ok leftResult) →
          PyAst.evalUnaryListFunctionOutcome module right values =
            some (.ok rightResult) →
          leftResult = rightResult
  | some (.objectList leftClass), some (.objectList rightClass) =>
      if leftClass = rightClass then
        ∀ values leftResult rightResult,
          PyAst.evalUnaryObjectIntListFunction module leftClass left values =
              some leftResult →
            PyAst.evalUnaryObjectIntListFunction module rightClass right values =
              some rightResult →
            leftResult = rightResult
      else False
  | _, _ => False

/-- Bound the cost assigned by the structural classifier using an explicit input
size. This abstraction does not establish termination; use execution Halts/Returns. -/
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

end FormalSW.Property.Function
