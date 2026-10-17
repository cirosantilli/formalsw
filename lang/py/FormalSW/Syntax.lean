import lang.py.FormalSW.Sorting
import lang.py.FormalSW.Globals

/-! Outcome predicates over deterministic executions. `_this_module` is supplied
by generated raw specifications; handwritten proofs bind it to their Python AST.
No predicate treats unsupported execution as evidence of termination. -/

namespace FormalSW.PyAst

syntax (name := pythonComparison) "python_comparison(" term ")" : term
macro_rules
  | `(python_comparison(($expr))) => `(python_comparison($expr))
  | `(python_comparison($left < $right)) =>
      `(comparison $(Lean.mkIdent `_this_module) .lt $left $right)
  | `(python_comparison($left <= $right)) =>
      `(comparison $(Lean.mkIdent `_this_module) .ltE $left $right)
  | `(python_comparison($left > $right)) =>
      `(comparison $(Lean.mkIdent `_this_module) .gt $left $right)
  | `(python_comparison($left >= $right)) =>
      `(comparison $(Lean.mkIdent `_this_module) .gtE $left $right)
  | `(python_comparison($left == $right)) =>
      `(comparison $(Lean.mkIdent `_this_module) .eq $left $right)
  | `(python_comparison($left != $right)) =>
      `(comparison $(Lean.mkIdent `_this_module) .notEq $left $right)
  | `(python_comparison($expr)) =>
      Lean.Macro.throwErrorAt expr
        "expected a comparison using <, <=, >, >=, ==, or !="

/-- The comparison finishes by raising an exception. -/
macro "Throws(" expr:term ")" : term => `(Execution.Throws (python_comparison($expr)))
/-- The comparison finishes normally with a boolean result. -/
macro "Returns(" expr:term ")" : term => `(Execution.Returns (python_comparison($expr)))
/-- The comparison finishes, either normally or with an exception. -/
macro "Halts(" expr:term ")" : term => `(Execution.Halts (python_comparison($expr)))

syntax (name := throwsCall) "Throws(" ident "(" term,* ")" ")" : term
syntax (name := returnsCall) "Returns(" ident "(" term,* ")" ")" : term
syntax (name := haltsCall) "Halts(" ident "(" term,* ")" ")" : term
syntax (name := divergesCall) "diverges(" ident "(" term,* ")" ")" : term

macro_rules (kind := throwsCall)
  | `(Throws($function:ident ($arguments,*))) => `(($function $arguments*).Throws)
macro_rules (kind := returnsCall)
  | `(Returns($function:ident ($arguments,*))) => `(($function $arguments*).Returns)
macro_rules (kind := haltsCall)
  | `(Halts($function:ident ($arguments,*))) => `(($function $arguments*).Halts)
macro_rules (kind := divergesCall)
  | `(diverges($function:ident ($arguments,*))) => `(($function $arguments*).Diverges)

end FormalSW.PyAst
