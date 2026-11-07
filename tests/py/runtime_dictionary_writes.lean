import lang.py.FormalSW.HeapRuntimeCostDictionaryWrites

open FormalSW.PyAst HeapCalls HeapCalls.Runtime
open FormalSW.PyAst.PrimitiveWork

namespace DictionaryWritesRuntimeRegression

/- Generated-shape source for:
   def put(d):
       d[1] = VALUE
       return d
   VALUE is supplied through globals at function entry. -/
def args : List Arg := [⟨"d", none, none⟩]
def body : List Stmt :=
  [.assign [.subscript (.name "d") (.constant (.int 1))] (.name "VALUE"),
    .return (.name "d")]
def program : Module := { body := [.functionDef "put" args none body] }
def context (value : Int) : Mutable.Globals := [("VALUE", .scalar (.int value))]

/-- The bound retains both table size and key widths, even with word arithmetic. -/
theorem put_returns (entries : List (Constant × Mutable.Value)) (value : Int) :
    ReturnsIn .word program "put" [.ref 0] [.dict entries]
      (mapLookup .collisionChain entries.length (MapWork.keyWork .word entries (.int 1)) + 16)
      (.ref 0) [.dict (ScalarDict.insert entries (.int 1) (.scalar (.int value)))]
      (context value) := by
  let env := functionEnv args body [.ref 0] (context value)
  have written : BlockContinuesIn (globals := context value) .word program env
      [.assign [.subscript (.name "d") (.constant (.int 1))] (.name "VALUE")]
      [.dict entries]
      (1 + 5 + mapLookup .collisionChain entries.length (MapWork.keyWork .word entries (.int 1)) + 5)
      env [.dict (ScalarDict.insert entries (.int 1) (.scalar (.int value)))] := by
    exact BlockContinuesIn.dictionary_setItem
      (address := 0) (key := .int 1) (entries := entries)
      (afterRhs := [.dict entries]) (afterArgs := [.dict entries])
      (by intro a b c equal; cases equal)
      (EvaluatesIn.lookup (by
        simp [env, functionEnv, args, body, context, blockLocals, assignedLocals, targetLocals]))
      (.cons (EvaluatesIn.lookup rfl) (.cons EvaluatesIn.constant .nil)) rfl
  have returned : BlockReturnsIn (globals := context value) .word program env body [.dict entries]
      (mapLookup .collisionChain entries.length (MapWork.keyWork .word entries (.int 1)) + 13)
      (.ref 0) [.dict (ScalarDict.insert entries (.int 1) (.scalar (.int value)))] := by
    exact (written.returns
      (BlockReturnsIn.return_value (expression := .name "d") (EvaluatesIn.lookup rfl))).mono (by omega)
  have called := BlockReturnsIn.function (name := "put") (values := [.ref 0])
    (args := args) (body := body) rfl rfl returned
  intro anchors stack
  exact (called anchors stack).mono (by simp [args] <;> omega)

/-- Insertion into an empty table and replacement in a nonempty table use the
same source rule, with different collision-chain budgets. -/
example : ReturnsIn .word program "put" [.ref 0] [.dict []] 18
    (.ref 0) [.dict [(.int 1, .scalar (.int 10))]] (context 10) :=
  put_returns [] 10

example : ReturnsIn .word program "put" [.ref 0]
    [.dict [(.int 1, .scalar (.int 10))]] 22
    (.ref 0) [.dict [(.int 1, .scalar (.int 20))]] (context 20) :=
  put_returns [(.int 1, .scalar (.int 10))] 20

example : ReturnsIn .word program "put" [.ref 0]
    [.dict [(.int 1, .scalar (.int 10)), (.int 2, .scalar (.int 30))]] 25
    (.ref 0) [.dict [(.int 1, .scalar (.int 20)), (.int 2, .scalar (.int 30))]] (context 20) :=
  put_returns [(.int 1, .scalar (.int 10)), (.int 2, .scalar (.int 30))] 20

/-- These are the existing setItem tariffs, including the reference write. -/
example : operation .word [.dict []] (.setItem (.scalar (.int 10)))
    [.ref 0, .scalar (.int 1)] = some 3 := by decide

example : operation .word [.dict [(.int 1, .scalar (.int 10))]]
    (.setItem (.scalar (.int 20))) [.ref 0, .scalar (.int 1)] = some 7 := by decide

example : operation .word [.dict [(.string "long key", .scalar (.int 10))]]
    (.setItem (.scalar (.int 20))) [.ref 0, .scalar (.int 1)] = some 23 := by decide

/-- The default globals argument also works. Storing an alias leaves unrelated
list potential intact, even when the dictionary refers to itself. -/
example (items : List Mutable.Value) :
    BlockContinuesIn .word program (fun _ => some (.ref 0))
      [.assign [.subscript (.name "d") (.constant (.int 1))] (.name "d")]
      [.dict [], .list items] 13 (fun _ => some (.ref 0))
      [.dict [(.int 1, .ref 0)], .list items] := by
  exact BlockContinuesIn.dictionary_setItem
    (address := 0) (key := .int 1) (entries := [])
    (afterRhs := [.dict [], .list items]) (afterArgs := [.dict [], .list items])
    (by intro a b c equal; cases equal)
    (EvaluatesIn.lookup rfl)
    (.cons (EvaluatesIn.lookup rfl) (.cons EvaluatesIn.constant .nil)) rfl

end DictionaryWritesRuntimeRegression
