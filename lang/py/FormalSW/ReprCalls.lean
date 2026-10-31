import lang.py.FormalSW.HeapCalls

/-! Scalar representation composes with caller effects without allocating heap objects. -/
namespace FormalSW.PyAst

namespace Calls

variable {module : Module} {env : ScalarEnv} {expression : Expr} {value : Constant}

theorem Evaluates.repr (evaluated : Evaluates module env expression value) :
    Evaluates module env (.builtinCall .repr [expression])
      (.string (Strings.reprValue value)) :=
  Evaluates.builtin (.cons evaluated .nil) rfl

end Calls

namespace HeapCalls

variable {globals : Mutable.Globals} {module : Module} {env : Env}
  {expression : Expr} {value : Constant} {heap middle : Heap}

theorem primitive_repr (value : Constant) (heap : Heap) :
    primitive (.builtin .repr) [.scalar value] heap =
      some (.ok (.scalar (.string (Strings.reprValue value))), heap) := rfl

theorem Evaluates.repr
    (evaluated : Evaluates (globals := globals) module env expression heap (.scalar value) middle) :
    Evaluates (globals := globals) module env (.builtinCall .repr [expression]) heap
      (.scalar (.string (Strings.reprValue value))) middle :=
  Evaluates.builtin (.cons evaluated .nil) rfl

end HeapCalls
end FormalSW.PyAst
