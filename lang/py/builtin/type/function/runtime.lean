import lang.py.builtin.type.dict
import lang.py.builtin.type.special
import lang.py.builtin.type.str

/-! Explicit state/effect interfaces for environment-dependent builtins. -/

namespace CleanXY.Py.Builtin.Function.Runtime

open CleanXY.Py.Builtin

abbrev Namespace (α : Type u) := Dict.Dict String α

structure RuntimeState (α : Type u) where
  globals : Namespace α := Dict.empty
  locals : Namespace α := Dict.empty
  standardOutput : Str.Str := []
  standardError : Str.Str := []
  standardInput : List Str.Str := []

inductive CompileMode where
  | exec
  | eval
  | single
deriving Repr, DecidableEq

def compile (source filename : String) (mode : CompileMode) (flags : Nat := 0)
    (optimization : Int := -1) : Special.CodeObject :=
  { source, filename,
    mode := match mode with | .exec => "exec" | .eval => "eval" | .single => "single"
    flags, optimization }

structure Evaluator (α : Type u) where
  eval : Special.CodeObject → Namespace α → Namespace α → Result α
  exec : Special.CodeObject → Namespace α → Namespace α → Result (Namespace α × Namespace α)

def eval (evaluator : Evaluator α) (code : Special.CodeObject)
    (state : RuntimeState α) : Result α := evaluator.eval code state.globals state.locals

def exec (evaluator : Evaluator α) (code : Special.CodeObject)
    (state : RuntimeState α) : Result (RuntimeState α) := do
  let (globals, locals) ← evaluator.exec code state.globals state.locals
  return { state with globals := globals, locals := locals }

def globals (state : RuntimeState α) : Namespace α := state.globals
def locals (state : RuntimeState α) : Namespace α := state.locals

def print (render : α → Result Str.Str) (objects : List α) (state : RuntimeState α)
    (separator : Str.Str := [32]) (ending : Str.Str := [10]) : Result (RuntimeState α) := do
  let rendered ← objects.mapM render
  let output := Subsequence.join separator rendered ++ ending
  return { state with standardOutput := state.standardOutput ++ output }

def input (state : RuntimeState α) (prompt : Str.Str := []) : Result (Str.Str × RuntimeState α) :=
  match state.standardInput with
  | [] => .error .eofError
  | line :: rest =>
      .ok (line, { state with
        standardInput := rest
        standardOutput := state.standardOutput ++ prompt })

structure FileSystem (Handle : Type u) where
  openFile : String → String → Result Handle

def «open» (filesystem : FileSystem Handle) (path mode : String) : Result Handle :=
  filesystem.openFile path mode

structure ImportSystem (Module : Type u) where
  importModule : String → List String → Int → Result Module

def «__import__» (system : ImportSystem Module) (name : String)
    (fromList : List String := []) (level : Int := 0) : Result Module :=
  system.importModule name fromList level

structure HelpSystem (α : Type u) where
  render : Option α → Result Str.Str

def help (system : HelpSystem α) (object : Option α := none) : Result Str.Str := system.render object

structure BreakpointHook (Args : Type u) (ResultType : Type v) where
  call : Args → Result ResultType

def breakpoint (hook : BreakpointHook Args ResultType) (args : Args) : Result ResultType :=
  hook.call args

end CleanXY.Py.Builtin.Function.Runtime
