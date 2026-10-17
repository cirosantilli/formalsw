import CleanXY

/-! A line-oriented JSON service for the CLI. All theorem/header/quotation
recognition below uses Lean's parser and syntax trees, including comments,
strings, raw strings, nested binders and parentheses. It does not elaborate
proofs; native quotation elaborators do that when checking the generated file. -/

open Lean CleanXY.PyAst

private partial def quotes (stx : Syntax) : Array Json := Id.run do
  let recognized := match stx with
    | `(Returns(py($s:str))) => some ("Returns", s.getString)
    | `(Throws(py($s:str))) => some ("Throws", s.getString)
    | `(Halts(py($s:str))) => some ("Halts", s.getString)
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

unsafe def main : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `CleanXY }] {} (loadExts := true)
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := do
      let request ← Json.parse line
      parseSpec env (← request.getStr?)
    let response := match result with
      | .ok value => value
      | .error error => Json.mkObj [("error", toJson error)]
    output.putStrLn response.compress
    output.flush
