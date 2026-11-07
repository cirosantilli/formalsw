import lang.py.FormalSW.HeapRuntimeCostDictionaries
import lang.py.FormalSW.HeapRuntimeCostScalarPairs

open FormalSW.PyAst FormalSW.PyAst.HeapCalls FormalSW.PyAst.HeapCalls.Runtime
open FormalSW.PyAst.PrimitiveWork

namespace DictionaryRuntimeRegression

def small : List (Constant × Constant) := [(.int 0, .int 0), (.int 1, .int 3), (.int 2, .int 3), (.int 3, .int 5), (.int 4, .int 4), (.int 5, .int 4), (.int 6, .int 3), (.int 7, .int 5), (.int 8, .int 5), (.int 9, .int 4), (.int 10, .int 3), (.int 11, .int 6), (.int 12, .int 6), (.int 13, .int 8), (.int 14, .int 8), (.int 15, .int 7), (.int 16, .int 7), (.int 17, .int 9), (.int 18, .int 8), (.int 19, .int 8)]
def tens : List (Constant × Constant) := [(.int 2, .int 6), (.int 3, .int 6), (.int 4, .int 5), (.int 5, .int 5), (.int 6, .int 5), (.int 7, .int 7), (.int 8, .int 6), (.int 9, .int 6)]

example : dictionaryLiteralBudget small = 771 := by decide
example : dictionaryLiteralBudget tens = 165 := by decide
example : dictionaryLiteralBudget [] = 2 := by decide

example : dictionaryContents [(.int 1, .int 3), (.bool true, .int 7)] =
    [(.int 1, .scalar (.int 7))] := by decide
example : dictionaryLiteralBudget [(.int 1, .int 3), (.int 1, .int 7)] = 23 := by decide
example : dictionaryLiteralBudget [(.string "long key", .int 3)] = 19 := by decide

example (module : Module) (env : HeapCalls.Env) (heap : Heap) :
    EvaluatesIn .word module env
      (.dict (small.map fun (key, value) => (.constant key, .constant value)))
      heap 771 (.ref heap.length) (heap ++ [.dict (dictionaryContents small)]) :=
  EvaluatesIn.dictionary_constants small

example (module : Module) (env : HeapCalls.Env) (heap : Heap) :
    EvaluatesIn .word module env
      (.dict (tens.map fun (key, value) => (.constant key, .constant value)))
      heap 165 (.ref heap.length) (heap ++ [.dict (dictionaryContents tens)]) :=
  EvaluatesIn.dictionary_constants tens

def pairs : List (Constant × Constant) := [(.int 1, .int 10), (.int 2, .int 20)]

example (module : Module) (env : HeapCalls.Env) (heap : Heap) :
    EvaluatesIn .word module env
      (.call (.attribute (.dict (pairs.map fun (k, v) => (.constant k, .constant v))) "get")
        [.constant (.int 1), .constant (.int 99)])
      heap 41 (.scalar (.int 10)) (heap ++ [.dict (dictionaryContents pairs)]) := by
  have found : (heap ++ [Mutable.Object.dict (dictionaryContents pairs)])[heap.length]? =
      some (.dict (dictionaryContents pairs)) := by simp
  exact EvaluatesIn.dictionary_get
    (by intro name equal; cases equal)
    (EvaluatesIn.dictionary_constants pairs) found
    (.cons EvaluatesIn.constant (.cons EvaluatesIn.constant .nil)) found
    (Or.inr ⟨.scalar (.int 99), rfl⟩)
    (by
      change Mutable.dictionaryGet heap.length (.scalar (.int 1)) (.scalar (.int 99)) _ = _
      rw [Mutable.dictionaryGet_scalar _ _ _ found]
      rfl)

example (module : Module) (env : HeapCalls.Env) (heap : Heap) :
    EvaluatesIn .word module env
      (.call (.attribute (.dict (pairs.map fun (k, v) => (.constant k, .constant v))) "get")
        [.constant (.int 3)])
      heap 38 (.scalar .none) (heap ++ [.dict (dictionaryContents pairs)]) := by
  have found : (heap ++ [Mutable.Object.dict (dictionaryContents pairs)])[heap.length]? =
      some (.dict (dictionaryContents pairs)) := by simp
  exact EvaluatesIn.dictionary_get
    (by intro name equal; cases equal)
    (EvaluatesIn.dictionary_constants pairs) found
    (.cons EvaluatesIn.constant .nil) found (Or.inl rfl)
    (by
      change Mutable.dictionaryGet heap.length (.scalar (.int 3)) (.scalar .none) _ = _
      rw [Mutable.dictionaryGet_scalar _ _ _ found]
      rfl)

example (left right : Int) (heap : Heap) :
    operation .word heap (.builtin .divmod) [.scalar (.int left), .scalar (.int right)] = some 5 := rfl

example : MapWork.lookup .collisionChain .word [.dict (dictionaryContents small)] 0
    (.scalar (.int 5)) = some 63 := by decide
example : MapWork.lookup .collisionChain .word [.dict (dictionaryContents tens)] 0
    (.scalar (.int 5)) = some 27 := by decide

/-- Negative dividends retain Python floor-division semantics while charging tuple creation. -/
example (module : Module) (env : HeapCalls.Env) (heap : Heap) :
    EvaluatesIn .word module env
      (.builtinCall .divmod [.constant (.int (-7)), .constant (.int 3)]) heap 12
      (.ref heap.length) (heap ++ [.tuple [.scalar (.int (-3)), .scalar (.int 2)]]) :=
  EvaluatesIn.divmod_ints EvaluatesIn.constant EvaluatesIn.constant (by decide)

end DictionaryRuntimeRegression
