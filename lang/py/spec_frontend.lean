import FormalSW

/-! A line-oriented JSON service for the CLI. All theorem/header/quotation
recognition below uses Lean's parser and syntax trees, including comments,
strings, raw strings, nested binders and parentheses. It does not elaborate
proofs; native quotation elaborators do that when checking the generated file. -/

open Lean FormalSW.PyAst

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

private def parseRequest (env : Environment) (line : String) : IO (Except String Json) := do
  match Json.parse line with
  | .error error => return .error error
  | .ok (.str text) => return parseSpec env text
  | .ok request =>
      match request.getObjValAs? String "imports" with
      | .error error => return .error error
      | .ok text =>
          let (imports, _, messages) ← Lean.Elab.parseImports text
          if messages.hasErrors then
            return .error "invalid Lean import header"
          return .ok (Json.mkObj [("imports", toJson (imports.map fun i => nameParts i.module))])

unsafe def main : IO Unit := do
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
