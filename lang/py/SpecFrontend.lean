import FormalSW

/-! A line-oriented JSON service for the CLI. All theorem/header/quotation
recognition below uses Lean's parser and syntax trees, including comments,
strings, raw strings, nested binders and parentheses. It does not elaborate
proofs; native quotation elaborators do that when checking the generated file. -/

open Lean FormalSW.PyAst

namespace FormalSW.SpecFrontend

private partial def quotes (stx : Syntax) : Array Json := Id.run do
  let recognized := match stx with
    | `(Returns(py($s:str))) => some ("Returns", s.getString)
    | `(Throws(py($s:str))) => some ("Throws", s.getString)
    | `(Halts(py($s:str))) => some ("Halts", s.getString)
    | `(CanDeadlock(py($s:str))) => some ("CanDeadlock", s.getString)
    | `(DeadlockFree(py($s:str))) => some ("DeadlockFree", s.getString)
    | `(CanDiverge(py($s:str))) => some ("CanDiverge", s.getString)
    | `(py($s:str)) => some ("condition", s.getString)
    | _ => none
  if let some (mode, expression) := recognized then
    return #[Json.mkObj [("mode", toJson mode), ("expression", toJson expression)]]
  return stx.getArgs.foldl (fun result arg => result ++ quotes arg) #[]

private def parseSpec (env : Environment) (text : String) : Except String Json := do
  let stx ← Parser.runParserCategory env `command (text ++ "\n:= by sorry")
  match stx with
  | `(theorem $name:ident $binders* : $type := $_) =>
      return Json.mkObj [
        ("name", toJson name.getId.toString),
        ("params", toJson (String.intercalate " " (binders.toList.map fun b => b.raw.reprint.getD ""))),
        ("type", toJson ((type.raw.reprint.getD "").trimAscii.toString)),
        ("quotes", Json.arr (quotes stx))]
  | _ => throw "expected a theorem name, optional binders, and a proposition"

private def nameParts : Name → List String
  | .anonymous => []
  | .str parent part => nameParts parent ++ [part]
  | .num parent part => nameParts parent ++ [toString part]

/-- Read binders through Lean's parsed syntax, never by scanning theorem text. -/
private partial def binderNames (stx : Syntax) : Array String :=
  if stx.isIdent then #[stx.getId.toString]
  else if stx.isOfKind ``Parser.Term.explicitBinder || stx.isOfKind ``Parser.Term.implicitBinder ||
      stx.isOfKind `Lean.bracketedExplicitBinders then binderNames stx[1]
  else if stx.isOfKind `Lean.unbracketedExplicitBinders || stx.isOfKind `Lean.binderIdent then
    binderNames stx[0]
  else if stx.isOfKind `null || stx.isOfKind `Lean.explicitBinders then
    stx.getArgs.foldl (fun names child => names ++ binderNames child) #[]
  else #[]

private def quantifier (stx : Syntax) : Option (Bool × Array String × String × Syntax) :=
  let index := if stx.isOfKind ``Parser.Term.forall then some 4
    else if stx.isOfKind `«term∃_,_» then some 3 else none
  index.map fun index =>
    (!stx.isOfKind ``Parser.Term.forall, binderNames stx[1],
      String.join ((stx.getArgs.extract 0 index).toList.map (fun s => s.reprint.getD "")), stx[index])

private partial def quantifiedNames (stx : Syntax) : Array String :=
  if stx.isOfKind ``Parser.Term.paren then quantifiedNames stx[1]
  else match quantifier stx with
    | some (_, names, _, body) => names ++ quantifiedNames body
    | none => #[]

private partial def guardType (stx : Syntax) (condition : String)
    (pending : Array String) (existential := false) : Except String String := do
  if pending.isEmpty then
    return s!"({condition}) {if existential then "∧" else "→"} ({stx.reprint.getD ""})"
  if stx.isOfKind ``Parser.Term.paren then
    return "(" ++ (← guardType stx[1] condition pending existential) ++ ")"
  let some (isExists, names, head, body) := quantifier stx
    | throw "Requires inputs are not bound by the leading quantifiers"
  let pending := pending.filter (fun name => !names.contains name)
  return head ++ "\n" ++ (← guardType body condition pending isExists)

private def guardRequest (env : Environment) (request : Json) : Except String Json := do
  let source ← request.getObjValAs? String "guard"
  let condition ← request.getObjValAs? String "condition"
  let captures ← request.getObjValAs? (Array String) "captures"
  let inputs ← request.getObjValAs? (Array String) "inputs"
  let bound ← request.getObjValAs? (Array String) "bound"
  let stx ← Parser.runParserCategory env `term source
  let names := quantifiedNames stx
  let mut pending := captures.filter (fun name => names.contains name && !bound.contains name)
  if captures.isEmpty && !(inputs.any bound.contains) then
    if let some name := names.find? inputs.contains then pending := #[name]
  let guarded ← guardType stx condition pending
  return Json.mkObj [("type", toJson guarded), ("bound", toJson names)]

private def parseRequest (env : Environment) (line : String) : IO (Except String Json) := do
  match Json.parse line with
  | .error error => return .error error
  | .ok (.str text) => return parseSpec env text
  | .ok request =>
      if (request.getObjVal? "guard").isOk then
        return guardRequest env request
      match request.getObjValAs? String "imports" with
      | .error error => return .error error
      | .ok text =>
          let (imports, _, messages) ← Lean.Elab.parseImports text
          if messages.hasErrors then
            return .error "invalid Lean import header"
          return .ok (Json.mkObj [("imports", toJson (imports.map fun i => nameParts i.module))])

unsafe def run : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `FormalSW }] {} (loadExts := true)
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result ← parseRequest env line
    let response := match result with
      | .ok value => value
      | .error error => Json.mkObj [("error", toJson error)]
    output.putStrLn response.compress
    output.flush

end FormalSW.SpecFrontend
