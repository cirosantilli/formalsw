import «.formalsw».lang.py.builtin.«function.py.ast»
import lang.py.builtin.function

namespace lang.py.builtin.function

open FormalSW.PyAst
open FormalSW.Py.Builtin

theorem modeled :
    FunctionAst.module.hasExactlyFunctions
      ["_digits", "_format_integer", "bin", "oct", "hex", "chr", "ord", "bool", "repr",
       "ascii", "format", "all", "any", "len", "iter", "aiter", "next", "anext",
       "reversed", "enumerate", "filter", "map", "max", "min", "sorted", "zip", "abs",
       "pow", "sum", "round", "callable", "delattr", "dir", "getattr", "hasattr", "id",
       "setattr", "vars", "hash", "isinstance", "issubclass", "type", "classmethod",
       "staticmethod"] = true := by
  rfl

theorem source_fingerprint : FunctionAst.module.fingerprint = 11409889112085856110 := by
  native_decide

theorem abs_equivalent (number : Int) :
    Function.Numeric.abs number = number.natAbs := by
  rfl

theorem sum_equivalent (values : List Int) (start : Int) :
    Function.Numeric.sum values start = values.foldl (· + ·) start := by
  rfl

end lang.py.builtin.function
