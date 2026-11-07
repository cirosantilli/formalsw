import lang.py.FormalSW.HeapRuntimeCostListWrites

namespace ListWritesRuntimeRegression
open FormalSW.PyAst HeapCalls HeapCalls.Runtime PrimitiveWork

private def program : Module := { body := [] }
private def env (value : Mutable.Value) (offset : Int) : Mutable.Env :=
  fun name => if name = "items" then some (.ref 0)
    else if name = "offset" then some (.scalar (.int offset)) else some value

/-- The source assignment writes any value by reference and preserves array size. -/
theorem write_at (arithmetic : Arithmetic) (items : List Mutable.Value) (value : Mutable.Value)
    (position : Nat) (inside : position < items.length) :
    BlockContinuesIn arithmetic program (env value position)
      [.assign [.subscript (.name "items") (.name "offset")] (.name "value")]
      [.list items] (11 + integer arithmetic position + integer arithmetic items.length)
      (env value position) [.list (items.set position value)] := by
  have written := BlockContinuesIn.list_setItem (globals := []) (arithmetic := arithmetic) (module := program)
    (env := env value position) (base := .name "items") (index := .name "offset")
    (expression := .name "value") (cr := 1) (ca := 5) (value := value)
    (address := 0) (offset := position) (items := items)
    (position := position) (afterRhs := [.list items]) (afterArgs := [.list items])
    (by intro a b c equal; cases equal)
    (EvaluatesIn.lookup rfl)
    (.cons (EvaluatesIn.lookup rfl) (.cons (EvaluatesIn.lookup rfl) .nil))
    rfl (by simp [Mutable.setItem, Mutable.index, show ¬ (position : Int) < 0 by omega,
      show ¬ items.length ≤ position by omega, Except.map])
  exact written.mono (by omega)

example (items : List Mutable.Value) (value : Mutable.Value) (position : Nat)
    (inside : position < items.length) :
    BlockContinuesIn .word program (env value position)
      [.assign [.subscript (.name "items") (.name "offset")] (.name "value")]
      [.list items] 13 (env value position) [.list (items.set position value)] :=
  write_at .word items value position inside

/-- Negative indices retain Python normalization, including a self-reference. -/
example : BlockContinuesIn .word program (env (.ref 0) (-1))
    [.assign [.subscript (.name "items") (.name "offset")] (.name "value")]
    [.list [.scalar (.int 7), .scalar (.int 8)]] 13 (env (.ref 0) (-1))
    [.list [.scalar (.int 7), .ref 0]] := by
  apply BlockContinuesIn.list_setItem (arithmetic := .word) (cr := 1) (ca := 5)
    (address := 0) (offset := -1)
    (items := [.scalar (.int 7), .scalar (.int 8)]) (position := 1)
    (afterRhs := [.list [.scalar (.int 7), .scalar (.int 8)]])
    (afterArgs := [.list [.scalar (.int 7), .scalar (.int 8)]])
  · intro a b c equal; cases equal
  · exact EvaluatesIn.lookup rfl
  · exact .cons (EvaluatesIn.lookup rfl) (.cons (EvaluatesIn.lookup rfl) .nil)
  · rfl
  · rfl

/-- The index width affects pricing; the width of a referenced value does not. -/
example : operation .word [.list [.scalar (.int 0)]] (.setItem (.scalar (.int (2^1000))))
    [.ref 0, .scalar (.int (2^100))] = some 3 := by decide
example : operation .bits [.list [.scalar (.int 0)]] (.setItem (.scalar (.int (2^1000))))
    [.ref 0, .scalar (.int (2^100))] = some 103 := by decide
example : operation .word [.list []] (.setItem (.ref 0)) [.ref 0, .scalar (.bool true)] = some 3 := rfl

/-- A failed bounds check still has an explicit tariff and leaves the heap intact. -/
example : RuntimeCost.Finishes (HeapCalls.step program 0) (charge .bits program)
    ⟨.operation (.setItem (.ref 0)) [.ref 0, .scalar (.int 4)], [], [.list []]⟩ 6
    (.ok ⟨.error ⟨"IndexError", []⟩, [], [.list []], 0⟩) := by
  exact .done rfl rfl

example : operation .word [.tuple []] (.setItem (.ref 0)) [.ref 0, .scalar (.int 0)] = none := rfl
example : operation .word [.list []] (.setItem (.ref 0)) [.ref 0, .scalar (.string "bad")] = none := rfl
example : operation .word [.dict []] (.setItem (.ref 0)) [.ref 0, .scalar (.int 0)] = some 3 := rfl
example : operation .word [.bytearray [0]] (.setItem (.scalar (.int 1))) [.ref 0, .scalar (.int 0)] = some 4 := rfl

#print axioms BlockContinuesIn.list_setItem
#print axioms write_at
end ListWritesRuntimeRegression
