import lang.py.builtin.type.core

/-! The synchronous context-manager protocol and `with` state transition. -/

namespace FormalSW.Py.Builtin.ContextManager

open FormalSW.Py.Builtin

structure ContextManager (State : Type u) (Value : Type v) where
  enter : State → Result (Value × State)
  exit : State → Option Error → Result (Bool × State)

/-- Execute a modeled `with` body and always invoke `__exit__`. -/
def withContext (manager : ContextManager State Value) (initial : State)
    (body : Value → State → Result (α × State)) : Result (Option α × State) := do
  let (value, entered) ← manager.enter initial
  match body value entered with
  | .ok (result, afterBody) =>
      let (_, exited) ← manager.exit afterBody none
      return (some result, exited)
  | .error error =>
      let (suppressed, exited) ← manager.exit entered (some error)
      if suppressed then return (none, exited) else throw error

end FormalSW.Py.Builtin.ContextManager
