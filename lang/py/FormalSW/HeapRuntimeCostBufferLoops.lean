import lang.py.FormalSW.HeapRuntimeCostBuffers

/-! Contiguous-buffer iteration reads one byte at a time. `Mutable.sequence`
describes the observable sequence; the target iterator does not copy it. -/
namespace FormalSW.PyAst.HeapCalls.Runtime
open PrimitiveWork

namespace EvaluatesIn

theorem bytearray (argument : EvaluatesIn arithmetic module env expression heap ca
    (.scalar (.bytes bytes)) middle) :
    EvaluatesIn arithmetic module env (.builtinCall .bytearray [expression]) heap
      (ca + bytes.length + 4) (.ref middle.length) (middle ++ [.bytearray bytes]) := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.builtinCall .bytearray [expression]) env, stack, heap⟩ 1
      ⟨.expr expression env, .arguments (.builtin .bytearray) [] [] env :: stack, heap⟩ := advance rfl rfl rfl
  have ready : Reaches arithmetic module anchors
      ⟨.value (.scalar (.bytes bytes)), .arguments (.builtin .bytearray) [] [] env :: stack, middle⟩ 1
      ⟨.operation (.builtin .bytearray) [.scalar (.bytes bytes)], stack, middle⟩ := advance rfl rfl rfl
  exact ((((initial.trans (argument anchors _)).trans ready).trans (bytearray_operation middle bytes))).mono (by omega)

theorem buffer_repeat (left : EvaluatesIn arithmetic module env a heap ca (.ref address) middle)
    (right : EvaluatesIn arithmetic module env b middle cb (.scalar (.int count)) afterRight)
    (found : afterRight[address]? = some (.bytearray bytes)) :
    EvaluatesIn arithmetic module env (.binOp a .mult b) heap
      (ca + cb + bytes.length * count.toNat + integer arithmetic count + 4)
      (.ref afterRight.length) (afterRight ++ [.bytearray (List.replicate count.toNat bytes).flatten]) := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.binOp a .mult b) env, stack, heap⟩ 1
      ⟨.expr a env, .binaryLeft .mult b env false :: stack, heap⟩ := advance rfl rfl rfl
  have ready : Reaches arithmetic module anchors
      ⟨.value (.ref address), .binaryLeft .mult b env false :: stack, middle⟩ 1
      ⟨.expr b env, .binaryRight .mult (.ref address) false :: stack, middle⟩ := advance rfl rfl rfl
  have copied : Reaches arithmetic module anchors
      ⟨.value (.scalar (.int count)), .binaryRight .mult (.ref address) false :: stack, afterRight⟩
      (bytes.length * count.toNat + integer arithmetic count + 2)
      ⟨.value (.ref afterRight.length), stack,
        afterRight ++ [.bytearray (List.replicate count.toNat bytes).flatten]⟩ := by
    apply RuntimeCost.Amortized.Reaches.next
      (amount := bytes.length * count.toNat + integer arithmetic count + 2)
    · simp [step, result, run, Mutable.binary, found, Mutable.allocateBuffer, Except.map,
        show (BinOp.mult == .mult) = true from rfl]
    · simp [charge, BufferWork.repetition, found, scalarNumber]
    · simp [potential, heapPotential, objectPotential]
  exact (((((initial.trans (left anchors _)).trans ready).trans (right anchors _)).trans copied)).mono (by omega)

theorem qualified_single (notAppend : field ≠ "append") (notAdd : field ≠ "add") (unbound : env alias = none)
    (argument : EvaluatesIn arithmetic module env expression heap ca value middle)
    (callee : ReturnsIn arithmetic module (alias ++ "." ++ field) [value] middle cc answer finalHeap) :
    EvaluatesIn arithmetic module env (.call (.attribute (.name alias) field) [expression]) heap
      (ca + cc + 2) answer finalHeap := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.call (.attribute (.name alias) field) [expression]) env, stack, heap⟩ 1
      ⟨.expr expression env, .arguments (.call (alias ++ "." ++ field)) [] [] env :: stack, heap⟩ :=
    advance (by simp [step, notAppend, notAdd, unbound, argumentsState]) (by simp [charge, notAppend, notAdd]) rfl
  have ready : Reaches arithmetic module anchors
      ⟨.value value, .arguments (.call (alias ++ "." ++ field)) [] [] env :: stack, middle⟩ 1
      ⟨.operation (.call (alias ++ "." ++ field)) [value], stack, middle⟩ := advance rfl rfl rfl
  exact ((((initial.trans (argument anchors _)).trans ready).trans (callee anchors stack))).mono (by omega)

end EvaluatesIn
namespace BlockContinuesIn

theorem buffer_enumerate_step (found : heap[address]? = some (.bytearray bytes))
    (sequence : Mutable.sequence (.ref address) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (rest : BlockContinuesIn .word module (setLocal (setLocal env index (.scalar (.int counter))) name value)
      (body ++ [Calls.loopContinuation body
        (.enumerateStepLoop index name (.ref address) (position + 1) (counter + 1) body otherwise)])
      heap budget finalEnv finalHeap) :
    BlockContinuesIn .word module env [.enumerateStepLoop index name (.ref address) position counter body otherwise]
      heap (budget + 7) finalEnv finalHeap := by
  intro following anchors stack
  have initial : Reaches .word module anchors
      ⟨.block ([.enumerateStepLoop index name (.ref address) position counter body otherwise] ++ following) env, stack, heap⟩ 7
      ⟨.block ((body ++ [Calls.loopContinuation body
        (.enumerateStepLoop index name (.ref address) (position + 1) (counter + 1) body otherwise)]) ++ following)
        (setLocal (setLocal env index (.scalar (.int counter))) name value), stack, heap⟩ :=
    advance (by simp [step, run, sequenceValue, sequence, item, List.append_assoc])
      (by simp [charge, found, integer]) rfl
  exact (initial.trans (rest following anchors stack)).mono (by omega)

theorem buffer_enumerate_done (found : heap[address]? = some (.bytearray bytes))
    (sequence : Mutable.sequence (.ref address) heap = some (.ok items, heap))
    (finished : items[position]? = none)
    (rest : BlockContinuesIn .word module env otherwise heap budget finalEnv finalHeap) :
    BlockContinuesIn .word module env [.enumerateStepLoop index name (.ref address) position counter body otherwise]
      heap (budget + 7) finalEnv finalHeap := by
  intro following anchors stack
  have initial : Reaches .word module anchors
      ⟨.block ([.enumerateStepLoop index name (.ref address) position counter body otherwise] ++ following) env, stack, heap⟩ 7
      ⟨.block (otherwise ++ following) env, stack, heap⟩ :=
    advance (by simp [step, run, sequenceValue, sequence, finished]) (by simp [charge, found, integer]) rfl
  exact (initial.trans (rest following anchors stack)).mono (by omega)

theorem for_buffer_enumerate (iterable : EvaluatesIn .word module env expression heap ca (.ref address) middle)
    (found : middle[address]? = some (.bytearray bytes))
    (sequence : Mutable.sequence (.ref address) middle = some (.ok items, middle))
    (rest : BlockContinuesIn .word module env
      [.enumerateStepLoop index name (.ref address) 0 0 body otherwise] middle budget finalEnv finalHeap) :
    BlockContinuesIn .word module env
      [.forIn (.tuple [.name index, .name name]) (.call (.name "enumerate") [expression]) body otherwise]
      heap (ca + budget + 6) finalEnv finalHeap := by
  intro following anchors stack
  have initial : Reaches .word module anchors
      ⟨.block ([.forIn (.tuple [.name index, .name name]) (.call (.name "enumerate") [expression]) body otherwise] ++ following) env,
        stack, heap⟩ 1
      ⟨.expr expression env, .enumerateSource index name (.constant (.int 0)) body otherwise following env :: stack, heap⟩ :=
    advance rfl rfl rfl
  have ready : Reaches .word module anchors
      ⟨.value (.ref address), .enumerateSource index name (.constant (.int 0)) body otherwise following env :: stack, middle⟩ 1
      ⟨.expr (.constant (.int 0)) env, .enumerateStart index name (.ref address) body otherwise following env :: stack, middle⟩ :=
    advance rfl rfl rfl
  have zero := EvaluatesIn.constant (arithmetic := .word) (module := module) (env := env) (heap := middle)
    (value := .int 0) anchors (.enumerateStart index name (.ref address) body otherwise following env :: stack)
  have enter : Reaches .word module anchors
      ⟨.value (.scalar (.int 0)), .enumerateStart index name (.ref address) body otherwise following env :: stack, middle⟩ 3
      ⟨.block ([.enumerateStepLoop index name (.ref address) 0 0 body otherwise] ++ following) env, stack, middle⟩ :=
    advance (by simp [step, run, enumerateStart, sequence, sequenceSource])
      (by simp [charge, found, scalarNumber, integer]) rfl
  exact (((((initial.trans (iterable anchors _)).trans ready).trans zero).trans enter).trans
    (rest following anchors stack)).mono (by omega)

end BlockContinuesIn
end FormalSW.PyAst.HeapCalls.Runtime
