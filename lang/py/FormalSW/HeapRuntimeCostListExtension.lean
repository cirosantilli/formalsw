import lang.py.FormalSW.HeapRuntimeCostControl

/-! In-place list concatenation retains the receiver and all aliases. Its
amortized budget pays for source reads, writes and capacity-doubling copies. -/
namespace FormalSW.PyAst.HeapCalls.Runtime
open PrimitiveWork

theorem list_extension (heap : Heap) (address source : Nat) (items additional : List Value)
    (destination : heap[address]? = some (.list items))
    (input : heap[source]? = some (.list additional)) :
    Reaches arithmetic module anchors
      ⟨.value (.ref source), .binaryRight .add (.ref address) true :: stack, heap⟩
      (4*additional.length+2)
      ⟨.value (.ref address), stack, heap.set address (.list (items ++ additional))⟩ := by
  apply RuntimeCost.Amortized.Reaches.next
    (amount := DynamicArray.appendMany items.length additional.length + additional.length + 2)
  · simp [step, result, run, inplace_add_lists heap address source items additional destination input]
  · simp [charge, listExtension, destination, input, Nat.add_assoc]
  · have paid := DynamicArray.appendMany_amortized items.length additional.length
    have changed := heapPotential_set heap address (.list items) (.list (items ++ additional)) destination
    simp only [objectPotential, List.length_append] at changed
    simp only [potential]
    omega

/-- Read the receiver before the RHS, but price and extend its contents after
RHS effects. The source may be the receiver itself. -/
theorem BlockContinuesIn.augAssign_list
    (lookup : env name = some (.ref address))
    (evaluated : EvaluatesIn arithmetic module env expression heap cost (.ref source) middle)
    (destination : middle[address]? = some (.list items))
    (input : middle[source]? = some (.list additional)) :
    BlockContinuesIn arithmetic module env [.augAssign (.name name) .add expression] heap
      (cost+4*additional.length+6) (setLocal env name (.ref address))
      (middle.set address (.list (items ++ additional))) := by
  intro following anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.block ([.augAssign (.name name) .add expression] ++ following) env, stack, heap⟩ 1
      ⟨.expr (.name name) env, .binaryLeft .add expression env true :: .assign name following env :: stack, heap⟩ :=
    advance rfl rfl rfl
  have loaded := EvaluatesIn.lookup (arithmetic := arithmetic) (module := module) (heap := heap)
    lookup anchors (.binaryLeft .add expression env true :: .assign name following env :: stack)
  have next : Reaches arithmetic module anchors
      ⟨.value (.ref address), .binaryLeft .add expression env true :: .assign name following env :: stack, heap⟩ 1
      ⟨.expr expression env, .binaryRight .add (.ref address) true :: .assign name following env :: stack, heap⟩ :=
    advance rfl rfl rfl
  have extended := list_extension (arithmetic := arithmetic) (module := module) (anchors := anchors)
    (stack := .assign name following env :: stack) middle address source items additional destination input
  have last : Reaches arithmetic module anchors
      ⟨.value (.ref address), .assign name following env :: stack, middle.set address (.list (items ++ additional))⟩ 1
      ⟨.block following (setLocal env name (.ref address)), stack, middle.set address (.list (items ++ additional))⟩ :=
    advance rfl rfl rfl
  exact (((((initial.trans loaded).trans next).trans (evaluated anchors _)).trans extended).trans last).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime
