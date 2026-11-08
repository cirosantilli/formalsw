import lang.py.FormalSW.HeapRuntimeCostLoopControl

namespace FormalSW.PyAst.HeapCalls.Runtime
open PrimitiveWork

namespace EvaluatesIn

theorem call (arguments : ArgumentsIn arithmetic module env 0 expressions heap ca values middle)
    (callee : ReturnsIn arithmetic module name values middle cc answer finalHeap) :
    EvaluatesIn arithmetic module env (.call (.name name) expressions) heap (ca + cc + 1) answer finalHeap := by
  intro anchors stack
  have first : Reaches arithmetic module anchors ⟨.expr (.call (.name name) expressions) env, stack, heap⟩ 1
      (argumentsState (.call name) env [] expressions stack heap) := advance rfl rfl (by cases expressions <;> rfl)
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (first.trans (arguments.reaches (.call name) anchors stack)).trans (callee anchors stack)

theorem list (arguments : ArgumentsIn arithmetic module env 0 expressions heap budget items middle) :
    EvaluatesIn arithmetic module env (.list expressions) heap (budget + 2*items.length + 3)
      (.ref middle.length) (middle ++ [.list items]) := by
  intro anchors stack
  have first : Reaches arithmetic module anchors ⟨.expr (.list expressions) env, stack, heap⟩ 1
      (argumentsState .list env [] expressions stack heap) := advance rfl rfl (by cases expressions <;> rfl)
  exact ((first.trans (arguments.reaches .list anchors stack)).trans (list_operation middle items)).mono (by omega)

theorem list_slice
    (arguments : ArgumentsIn arithmetic module env 0
      [base, lower.getD (.constant .none), upper.getD (.constant .none), stride.getD (.constant .none)]
      heap budget [.ref address, first, last, stepValue] middle)
    (found : middle[address]? = some (.list items))
    (evaluated : Mutable.getSlice (.ref address) first last stepValue middle =
      some (.ok (.ref middle.length), middle ++ [.list selected]))
    (priced : SequenceWork.slice arithmetic items.length first last stepValue = some work) :
    EvaluatesIn arithmetic module env (.subscript base (.slice lower upper stride)) heap
      (budget + work + selected.length + 2) (.ref middle.length) (middle ++ [.list selected]) := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.subscript base (.slice lower upper stride)) env, stack, heap⟩ 1
      (argumentsState .slice env [] [base, lower.getD (.constant .none),
        upper.getD (.constant .none), stride.getD (.constant .none)] stack heap) := advance rfl rfl rfl
  have copied : Reaches arithmetic module anchors
      ⟨.operation .slice [.ref address, first, last, stepValue], stack, middle⟩ (work+selected.length+1)
      ⟨.value (.ref middle.length), stack, middle ++ [.list selected]⟩ := by
    apply RuntimeCost.Amortized.Reaches.next (amount := work+1)
    · simp [step, result, run, primitive, evaluated]
    · simp [charge, operation, found, priced]
    · have credits := DynamicArray.potential_le selected.length
      simp only [potential, heapPotential_allocate]
      omega
  exact ((initial.trans (arguments.reaches .slice anchors stack)).trans copied).mono (by omega)

theorem list_suffix_word
    (evaluated : EvaluatesIn .word module env receiver heap cost (.ref address) middle)
    (found : middle[address]? = some (.list items)) (start : Nat) :
    EvaluatesIn .word module env
      (.subscript receiver (.slice (some (.constant (.int start))) none none)) heap
      (cost+7*(items.length-start)+216) (.ref middle.length) (middle ++ [.list (items.drop start)]) := by
  have copied := list_slice (lower := some (.constant (.int start))) (upper := none) (stride := none)
    (ArgumentsIn.cons evaluated (ArgumentsIn.cons EvaluatesIn.constant
      (ArgumentsIn.cons EvaluatesIn.constant (ArgumentsIn.cons EvaluatesIn.constant ArgumentsIn.nil)))) found
    (Mutable.getSlice_list_suffix middle address items start found) (SequenceWork.slice_suffix items.length start)
  exact copied.mono (by simp; omega)

theorem concatenate
    (left : EvaluatesIn .word module env a heap ca (.ref leftAddress) middle)
    (right : EvaluatesIn .word module env b middle cb (.ref rightAddress) afterRight)
    (leftFound : afterRight[leftAddress]? = some (.list ls))
    (rightFound : afterRight[rightAddress]? = some (.list rs)) :
    EvaluatesIn .word module env (.binOp a .add b) heap
      (ca + cb + 2*(ls.length+rs.length) + 6)
      (.ref afterRight.length) (afterRight ++ [.list (ls ++ rs)]) := by
  intro anchors stack
  have initial : Reaches .word module anchors ⟨.expr (.binOp a .add b) env, stack, heap⟩ 1
      ⟨.expr a env, .binaryLeft .add b env false :: stack, heap⟩ := advance rfl rfl rfl
  have next : Reaches .word module anchors ⟨.value (.ref leftAddress), .binaryLeft .add b env false :: stack, middle⟩ 1
      ⟨.expr b env, .binaryRight .add (.ref leftAddress) false :: stack, middle⟩ := advance rfl rfl rfl
  have copied : Reaches .word module anchors
      ⟨.value (.ref rightAddress), .binaryRight .add (.ref leftAddress) false :: stack, afterRight⟩
      (2*(ls.length+rs.length)+4) ⟨.value (.ref afterRight.length), stack, afterRight ++ [.list (ls ++ rs)]⟩ := by
    apply RuntimeCost.Amortized.Reaches.next (amount := ls.length+rs.length+4)
    · simp [step, result, run, Mutable.binary, show (BinOp.add == BinOp.add) = true from rfl,
        leftFound, rightFound, Mutable.array, Mutable.allocate, Except.map]
    · simp [charge, SequenceWork.concatenate, leftFound, rightFound, integer]
    · have credits := DynamicArray.potential_le (ls.length+rs.length)
      simp only [potential, heapPotential_allocate, List.length_append]
      omega
  exact ((((initial.trans (left anchors _)).trans next).trans (right anchors _)).trans copied).mono (by omega)

theorem not_list (evaluated : EvaluatesIn arithmetic module env expression heap cost (.ref address) middle)
    (found : middle[address]? = some (.list items)) :
    EvaluatesIn arithmetic module env (.unaryOp .not expression) heap (cost+2)
      (.scalar (.bool items.isEmpty)) middle := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors ⟨.expr (.unaryOp .not expression) env, stack, heap⟩ 1
      ⟨.expr expression env, .unary .not :: stack, heap⟩ := advance rfl rfl rfl
  have next : Reaches arithmetic module anchors ⟨.value (.ref address), .unary .not :: stack, middle⟩ 1
      ⟨.value (.scalar (.bool items.isEmpty)), stack, middle⟩ :=
    advance (by simp [step, result, run, HeapCalls.unary, Mutable.truth, found])
      (by simp [charge, truth, found]) rfl
  exact ((initial.trans (evaluated anchors _)).trans next).mono (by omega)

theorem list_conditional
    (condition : EvaluatesIn arithmetic module env test heap ct (.ref address) middle)
    (found : middle[address]? = some (.list items))
    (tested : Mutable.truth (.ref address) middle = some (.ok flag, middle))
    (branch : EvaluatesIn arithmetic module env (if flag then yes else no) middle cb answer finalHeap) :
    EvaluatesIn arithmetic module env (.ifExp test yes no) heap (ct+cb+2) answer finalHeap := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.expr (.ifExp test yes no) env, stack, heap⟩ 1
      ⟨.expr test env, .conditional yes no env :: stack, heap⟩ := advance rfl rfl rfl
  have chosen : Reaches arithmetic module anchors
      ⟨.value (.ref address), .conditional yes no env :: stack, middle⟩ 1
      ⟨.expr (if flag then yes else no) env, stack, middle⟩ :=
    advance (by simp [step, run, tested]) (by simp [charge, truth, found]) rfl
  exact (((first.trans (condition anchors _)).trans chosen).trans (branch anchors stack)).mono (by omega)

end EvaluatesIn
end FormalSW.PyAst.HeapCalls.Runtime
