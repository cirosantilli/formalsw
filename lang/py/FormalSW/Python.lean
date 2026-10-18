import Lean

namespace FormalSW.PyAst

private partial def pythonRoot (directory : System.FilePath) : IO System.FilePath := do
  if ← (directory / "lang" / "py" / "data_ast.py").pathExists then
    return directory
  let some parent := directory.parent
    | throw (IO.userError "cannot locate the formalsw Python package beside its Lean modules")
  pythonRoot parent

/-- Locate bundled compilers through Lean's source or object search path while
retaining the caller's working directory for Python source references. -/
def runPythonCompiler (moduleName : String) (args : Array String) : IO IO.Process.Output := do
  let source? ← (← Lean.getSrcSearchPath).findWithExt "lean" `lang.py.FormalSW.Model
  let modulePath ← match source? with
    | some source => pure source
    | none => Lean.findOLean `lang.py.FormalSW.Model
  let root ← pythonRoot (← IO.FS.realPath modulePath)
  let existing := ((← IO.getEnv "PYTHONPATH").map System.SearchPath.parse).getD []
  let path : System.SearchPath := root :: existing
  IO.Process.output {
    cmd := "python3", args := #["-m", moduleName] ++ args
    env := #[("PYTHONPATH", some path.toString)] }

end FormalSW.PyAst
