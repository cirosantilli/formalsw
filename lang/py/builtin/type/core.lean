/-! Shared result and error types for Python builtin models. -/

namespace FormalSW.Py.Builtin

/-- Python exceptions raised by the non-floating-point builtin model. -/
inductive Error where
  | attributeError (message : String)
  | eofError (message : String := "EOF when reading a line")
  | importError (message : String)
  | indexError (message : String)
  | keyError (message : String)
  | memoryError (message : String)
  | nameError (message : String)
  | overflowError (message : String)
  | runtimeError (message : String)
  | stopAsyncIteration
  | stopIteration
  | typeError (message : String)
  | unicodeError (message : String)
  | valueError (message : String)
  | zeroDivisionError (message : String)
  /-- The requested result necessarily belongs to the deliberately omitted float model. -/
  | floatingPointExcluded (operation : String)
deriving Repr, DecidableEq

/-- A builtin either returns a value or raises a modeled Python exception. -/
abbrev Result (α : Type u) := Except Error α

end FormalSW.Py.Builtin
