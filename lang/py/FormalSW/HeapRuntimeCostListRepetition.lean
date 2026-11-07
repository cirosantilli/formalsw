import lang.py.FormalSW.HeapRuntimeCostControl

/-! Fresh list repetition copies references and prepays the output array potential. -/
namespace FormalSW.PyAst.HeapCalls.Runtime.EvaluatesIn
open PrimitiveWork

theorem list_repeat (left : EvaluatesIn arithmetic module env a heap ca (.ref address) middle)
    (right : EvaluatesIn arithmetic module env b middle cb (.scalar (.int count)) afterRight)
    (found : afterRight[address]? = some (.list items)) :
    EvaluatesIn arithmetic module env (.binOp a .mult b) heap
      (ca + cb + 2 * (items.length * count.toNat) + integer arithmetic count + 4)
      (.ref afterRight.length) (afterRight ++ [.list (List.replicate count.toNat items).flatten]) := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.binOp a .mult b) env, stack, heap⟩ 1
      ⟨.expr a env, .binaryLeft .mult b env false :: stack, heap⟩ := advance rfl rfl rfl
  have ready : Reaches arithmetic module anchors
      ⟨.value (.ref address), .binaryLeft .mult b env false :: stack, middle⟩ 1
      ⟨.expr b env, .binaryRight .mult (.ref address) false :: stack, middle⟩ := advance rfl rfl rfl
  have copied : Reaches arithmetic module anchors
      ⟨.value (.scalar (.int count)), .binaryRight .mult (.ref address) false :: stack, afterRight⟩
      (2 * (items.length * count.toNat) + integer arithmetic count + 2)
      ⟨.value (.ref afterRight.length), stack,
        afterRight ++ [.list (List.replicate count.toNat items).flatten]⟩ := by
    apply RuntimeCost.Amortized.Reaches.next
      (amount := items.length * count.toNat + integer arithmetic count + 2)
    · simp [step, result, run, Mutable.binary, Mutable.array, found, Mutable.allocate, Except.map,
        show (BinOp.mult == .mult) = true from rfl]
    · simp [charge, BufferWork.repetition, SequenceWork.repetition, found, scalarNumber]
    · have paid := DynamicArray.potential_le (List.replicate count.toNat items).flatten.length
      have size : (List.replicate count.toNat items).flatten.length = items.length * count.toNat := by
        simp [Nat.mul_comm]
      rw [size] at paid
      simp only [potential, heapPotential_allocate, size]
      omega
  exact (((((initial.trans (left anchors _)).trans ready).trans (right anchors _)).trans copied)).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime.EvaluatesIn
