import Lean
import lang.py.CleanXY.Syntax
import lang.py.CleanXY.PyValue

/-! Lean parses the surrounding specification and the string literal. Python
parses only the decoded string. Captures are resolved by Lean's elaborator;
the Python compiler returns a closed lambda, so generated locals cannot capture
variables in the surrounding theorem. No theorem text is rewritten. -/

namespace CleanXY.PyAst

open Lean Elab Term Meta

syntax (name := pythonQuote) "py(" str ")" : term
syntax (name := pythonReturns) "Returns(" "py(" str ")" ")" : term
syntax (name := pythonThrows) "Throws(" "py(" str ")" ")" : term
syntax (name := pythonHalts) "Halts(" "py(" str ")" ")" : term
syntax (name := pythonCanDeadlock) "CanDeadlock(" "py(" str ")" ")" : term
syntax (name := pythonDeadlockFree) "DeadlockFree(" "py(" str ")" ")" : term
syntax (name := pythonCanDiverge) "CanDiverge(" "py(" str ")" ")" : term

/-- Bind the source module and enclosing function for Python quotations. -/
syntax (name := pythonContext) "python_context " str str term " in " term : term

private def compileQuote (source : TSyntax `str) (mode : String) : TermElabM Lean.Expr := do
  let options ← getOptions
  let path := options.get `cleanxy.pythonSource ""
  let function := options.get `cleanxy.pythonFunction ""
  if path.isEmpty then
    throwError "py requires python_context with a Python source file and enclosing function"
  let moduleName := options.get `cleanxy.pythonModuleName Name.anonymous
  let some context := (← getLCtx).findFromUserName? moduleName
    | throwError "missing Python module context"
  let request := Json.mkObj [
    ("source", toJson path), ("function", toJson function),
    ("expression", toJson source.getString), ("mode", toJson mode)]
  let result ← IO.Process.output {
    cmd := "python3", args := #["-m", "lang.py.quotation", request.compress] }
  if result.exitCode != 0 then
    throwError "Python quotation compiler failed: {result.stderr}"
  let response ← ofExcept (Json.parse result.stdout)
  if let .ok message := response.getObjValAs? String "unsupported" then
    throwError "unsupported Python constructs: {message}"
  if let .ok message := response.getObjValAs? String "error" then
    throwError "{message}"
  let captures ← ofExcept (response.getObjValAs? (Array String) "captures")
  let code ← ofExcept (response.getObjValAs? String "term")
  let stx ← ofExcept (Parser.runParserCategory (← getEnv) `term code)
  let compiled ← withoutAutoBoundImplicit <| withLCtx {} #[] <|
    withTheReader Core.Context (fun ctx =>
      { ctx with currNamespace := `CleanXY.PyAst, openDecls := [] }) <|
      elabTerm stx none
  let mut arguments := #[context.toExpr]
  for name in captures do
    let value ← withoutAutoBoundImplicit <|
      elabTermEnsuringType (mkIdentFrom source (Name.mkSimple name)) (some (mkConst ``PyValue))
    -- Attribute the captured variable use to the original string literal for
    -- editor information and Lean's unused-variable linter.
    addTermInfo' source value
    arguments := arguments.push value
  return mkAppN compiled arguments

elab_rules (kind := pythonQuote) : term
  | `(py($source:str)) => compileQuote source "condition"

elab_rules (kind := pythonReturns) : term
  | `(Returns(py($source:str))) => compileQuote source "Returns"

elab_rules (kind := pythonThrows) : term
  | `(Throws(py($source:str))) => compileQuote source "Throws"

elab_rules (kind := pythonHalts) : term
  | `(Halts(py($source:str))) => compileQuote source "Halts"

elab_rules (kind := pythonCanDeadlock) : term
  | `(CanDeadlock(py($source:str))) => compileQuote source "CanDeadlock"

elab_rules (kind := pythonDeadlockFree) : term
  | `(DeadlockFree(py($source:str))) => compileQuote source "DeadlockFree"

elab_rules (kind := pythonCanDiverge) : term
  | `(CanDiverge(py($source:str))) => compileQuote source "CanDiverge"

elab_rules (kind := pythonContext) : term
  | `(python_context $source:str $function:str $module:term in $body:term) => do
      let module ← elabTermEnsuringType module (some (mkConst ``Module))
      let moduleName ← mkFreshUserName `_cleanxy_python_module
      let options := (← getOptions).set `cleanxy.pythonSource source.getString
        |>.set `cleanxy.pythonFunction function.getString
        |>.set `cleanxy.pythonModuleName moduleName
      withOptions (fun _ => options) do
        withLetDecl moduleName (mkConst ``Module) module fun moduleLocal => do
          let result ← elabTerm body none
          return result.replaceFVar moduleLocal module

end CleanXY.PyAst
