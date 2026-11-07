import lang.py.FormalSW.HeapRuntimeCostListAugAssign
import lang.py.FormalSW.HeapRuntimeCostListCopies

namespace ListAugAssignRuntimeRegression
open FormalSW.PyAst HeapCalls HeapCalls.Runtime PrimitiveWork

private def program : Module := { body := [] }
private def env : Mutable.Env := fun _ => some (.ref 0)

/-- A negative index is normalized at both the read and write. -/
theorem negative_update (arithmetic : Arithmetic) (work : Nat)
    (priced : PrimitiveWork.binary arithmetic .add (.int 8) (.int 3) = some work) :
    BlockContinuesIn arithmetic program env
      [.augAssign (.subscript (.name "xs") (.constant (.int (-1)))) .add (.constant (.int 3))]
      [.list [.scalar (.int 7), .scalar (.int 8)]]
      (3 + 2 * integer arithmetic (-1) + integer arithmetic 2 + integer arithmetic 2 + work + 8)
      env [.list [.scalar (.int 7), .scalar (.int 11)]] := by
  apply BlockContinuesIn.list_augAssignItem (cb := 1) (ci := 1) (cr := 1)
    (address := 0) (offset := -1) (left := .int 8) (right := .int 3)
    (updated := .scalar (.int 11))
    (items := [.scalar (.int 7), .scalar (.int 8)])
    (current := [.scalar (.int 7), .scalar (.int 8)]) (position := 1)
    (afterReceiver := [.list [.scalar (.int 7), .scalar (.int 8)]])
    (afterIndex := [.list [.scalar (.int 7), .scalar (.int 8)]])
    (afterRhs := [.list [.scalar (.int 7), .scalar (.int 8)]])
  · intro a b c equal; cases equal
  · exact EvaluatesIn.lookup rfl
  · exact EvaluatesIn.constant
  · rfl
  · rfl
  · exact EvaluatesIn.constant
  · rfl
  · exact priced
  · rfl
  · rfl

example : BlockContinuesIn .word program env
    [.augAssign (.subscript (.name "xs") (.constant (.int (-1)))) .add (.constant (.int 3))]
    [.list [.scalar (.int 7), .scalar (.int 8)]] 16
    env [.list [.scalar (.int 7), .scalar (.int 11)]] := negative_update .word 1 rfl

example : BlockContinuesIn .bits program env
    [.augAssign (.subscript (.name "xs") (.constant (.int (-1)))) .add (.constant (.int 3))]
    [.list [.scalar (.int 7), .scalar (.int 8)]] 23
    env [.list [.scalar (.int 7), .scalar (.int 11)]] := negative_update .bits 6 (by decide)

private def grow : Module :=
  { body := [.functionDef "grow" [⟨"xs", none, none⟩] none
    [.expr (.call (.attribute (.name "xs") "append") [.constant (.int 100)]),
      .return (.constant (.int 3))]] }

/-- `xs[-1] += grow(alias)` reads 7, then the RHS appends 100 through the
alias and returns 3. The write normalizes -1 against the grown list, leaving
the first element at 7 and replacing the appended 100 with 10. Reading after
the RHS or saving the normalized position would give a different result. -/
theorem rhs_alias_growth : BlockContinuesIn .word grow env
    [.augAssign (.subscript (.name "xs") (.constant (.int (-1)))) .add
      (.call (.name "grow") [.name "alias"])]
    [.list [.scalar (.int 7)]] 34 env [.list [.scalar (.int 7), .scalar (.int 10)]] := by
  have called : ReturnsIn .word grow "grow" [.ref 0] [.list [.scalar (.int 7)]]
      (1 + 1 + 1 + 13) (.scalar (.int 3)) [.list [.scalar (.int 7), .scalar (.int 100)]] := by
    apply BlockReturnsIn.function (args := [⟨"xs", none, none⟩]) (budget := 13) rfl rfl
    have appended := EvaluatesIn.append (globals := []) (arithmetic := .word) (module := grow)
      (base := .name "xs") (expression := .constant (.int 100))
      (heap := [.list [.scalar (.int 7)]]) (address := 0)
      (old := [.scalar (.int 7)]) (current := [.scalar (.int 7)])
      (env := functionEnv [⟨"xs", none, none⟩]
        [.expr (.call (.attribute (.name "xs") "append") [.constant (.int 100)]),
          .return (.constant (.int 3))] [.ref 0] [])
      (EvaluatesIn.lookup rfl) rfl EvaluatesIn.constant rfl
    exact (BlockContinuesIn.discard appended).returns
      (BlockReturnsIn.return_value EvaluatesIn.constant)
  have rhs := EvaluatesIn.call (env := env) (expressions := [.name "alias"])
    (ArgumentsIn.cons (EvaluatesIn.lookup rfl) ArgumentsIn.nil) called
  apply BlockContinuesIn.list_augAssignItem (cb := 1) (ci := 1) (cr := 19)
    (address := 0) (offset := -1) (left := .int 7) (right := .int 3) (work := 1)
    (updated := .scalar (.int 10))
    (items := [.scalar (.int 7)]) (current := [.scalar (.int 7), .scalar (.int 100)])
    (position := 1) (afterReceiver := [.list [.scalar (.int 7)]])
    (afterIndex := [.list [.scalar (.int 7)]])
    (afterRhs := [.list [.scalar (.int 7), .scalar (.int 100)]])
  · intro a b c equal; cases equal
  · exact EvaluatesIn.lookup rfl
  · exact EvaluatesIn.constant
  · rfl
  · rfl
  · exact rhs
  · rfl
  · rfl
  · rfl
  · rfl

/-- The write tariff observes the current length, including RHS growth. -/
example : charge .bits program
    ⟨.value (.scalar (.int 10)), [.writeItem (.ref 0) (.scalar (.int (-1))) [] env],
      [.list [.scalar (.int 7)]]⟩ = some 4 := by decide
example : charge .bits program
    ⟨.value (.scalar (.int 10)), [.writeItem (.ref 0) (.scalar (.int (-1))) [] env],
      [.list [.scalar (.int 7), .scalar (.int 100)]]⟩ = some 5 := by decide

/-- The arithmetic step retains the selected operand-width policy. -/
example : charge .word program
    ⟨.value (.scalar (.int 3)), [.binaryRight .add (.scalar (.int (2^100))) true], []⟩ = some 2 := by decide
example : charge .bits program
    ⟨.value (.scalar (.int 3)), [.binaryRight .add (.scalar (.int (2^100))) true], []⟩ = some 104 := by decide

/-- A failed read raises before `grow` can run; no RHS mutation occurs. -/
theorem invalid_read_skips_rhs : RuntimeCost.Finishes (HeapCalls.step grow 0) (charge .word grow)
    ⟨.block [.augAssign (.subscript (.name "xs") (.constant (.int 4))) .add
      (.call (.name "grow") [.name "alias"])] env, [], [.list []]⟩ 8
    (.ok ⟨.error ⟨"IndexError", []⟩, [], [.list []], 0⟩) := by
  let trace : { cost : Nat // RuntimeCost.Finishes (HeapCalls.step grow 0) (charge .word grow)
      ⟨.block [.augAssign (.subscript (.name "xs") (.constant (.int 4))) .add
        (.call (.name "grow") [.name "alias"])] env, [], [.list []]⟩ cost
      (.ok ⟨.error ⟨"IndexError", []⟩, [], [.list []], 0⟩) } := by
    apply Subtype.mk
    repeat first
      | exact RuntimeCost.Finishes.done rfl rfl
      | apply RuntimeCost.Finishes.next <;> first | rfl | skip
  exact trace.property

example : RuntimeCost.Finishes (HeapCalls.step program 0) (charge .bits program)
    ⟨.value (.scalar (.int 1)), [.writeItem (.ref 0) (.scalar (.int (-4))) [] env], [.list []]⟩ 6
    (.ok ⟨.error ⟨"IndexError", []⟩, [], [.list []], 0⟩) := by
  exact .done rfl rfl

/-- Map accesses remain size-sensitive, with the selected representation. -/
example : charge .word program
    ⟨.value (.scalar (.int 0)), [.augmentItemIndex (.ref 0) .add (.constant (.int 1)) [] env],
      [.dict [(.int 0, .scalar (.int 7)), (.int 1, .scalar (.int 9))]]⟩ = some 10 := rfl
example : charge .word program
    ⟨.value (.scalar (.int 8)), [.writeItem (.ref 0) (.scalar (.int 0)) [] env],
      [.dict [(.int 0, .scalar (.int 7)), (.int 1, .scalar (.int 9))]]⟩ = some 11 := rfl
example : charge .word program
    ⟨.value (.scalar (.int 0)), [.augmentItemIndex (.ref 0) .add (.constant (.int 1)) [] env],
      [.dict [(.int 0, .scalar (.int 7)), (.int 1, .scalar (.int 9))]]⟩ .balancedTree = some 16 := by decide
example : charge .word program
    ⟨.value (.scalar (.int 8)), [.writeItem (.ref 0) (.scalar (.int 0)) [] env],
      [.dict [(.int 0, .scalar (.int 7)), (.int 1, .scalar (.int 9))]]⟩ .balancedTree = some 17 := by decide

/-- Buffer writes still pay for byte conversion in addition to indexing. -/
example : charge .word program
    ⟨.value (.scalar (.int 0)), [.augmentItemIndex (.ref 0) .add (.constant (.int 1)) [] env],
      [.bytearray [7]]⟩ = some 4 := rfl
example : charge .word program
    ⟨.value (.scalar (.int 8)), [.writeItem (.ref 0) (.scalar (.int 0)) [] env],
      [.bytearray [7]]⟩ = some 5 := rfl

/-- Slice targets, unsupported key protocols and immutable writes stay unpriced. -/
example : charge .word program
    ⟨.block [.augAssign (.subscript (.name "xs") (.slice none none none)) .add
      (.constant (.int 1))] env, [], [.list []]⟩ = none := rfl
example : charge .word program
    ⟨.value (.ref 1), [.augmentItemIndex (.ref 0) .add (.constant (.int 1)) [] env],
      [.dict [], .list []]⟩ = none := rfl
example : charge .word program
    ⟨.value (.scalar (.int 1)), [.writeItem (.ref 0) (.ref 1) [] env],
      [.dict [], .list []]⟩ = none := rfl
example : charge .word program
    ⟨.value (.scalar (.int 1)), [.writeItem (.ref 0) (.scalar (.int 0)) [] env],
      [.tuple [.scalar (.int 7)]]⟩ = none := rfl

#print axioms BlockContinuesIn.list_augAssignItem
#print axioms negative_update
#print axioms rhs_alias_growth
#print axioms invalid_read_skips_rhs
end ListAugAssignRuntimeRegression
