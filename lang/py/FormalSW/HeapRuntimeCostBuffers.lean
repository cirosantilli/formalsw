import lang.py.FormalSW.HeapRuntimeCostControl

namespace FormalSW.PyAst.HeapCalls.Runtime
/-- The index records already-evaluated arguments, whose continuation frames
have their own costs in the interpreter. -/
inductive ArgumentsIn (arithmetic : PrimitiveWork.Arithmetic) (module : Module) (env : Env) :
    Nat → List Expr → Heap → Nat → List Value → Heap → (globals : Mutable.Globals := []) → Prop
  | nil : ArgumentsIn (globals := globals) arithmetic module env completed [] heap 0 [] heap
  | cons (first : EvaluatesIn (globals := globals) arithmetic module env expression heap ca value middle)
      (rest : ArgumentsIn (globals := globals) arithmetic module env (completed + 1) expressions middle cb values finalHeap) :
      ArgumentsIn (globals := globals) arithmetic module env completed (expression :: expressions) heap
        (ca + (completed + 1) + cb) (value :: values) finalHeap

variable {globals : Mutable.Globals}
open PrimitiveWork

/-- Buffer allocation carries no dynamic-list credits. -/
theorem bytearray_operation (heap : Heap) (bytes : List UInt8) :
    Reaches (globals := globals) arithmetic module anchors
      ⟨.operation (.builtin .bytearray) [.scalar (.bytes bytes)], stack, heap⟩ (bytes.length + 2)
      ⟨.value (.ref heap.length), stack, heap ++ [.bytearray bytes]⟩ := by
  apply RuntimeCost.Amortized.Reaches.next (amount := bytes.length + 2)
  · simp [step, result, run, primitive, Mutable.bytearray, Mutable.byteValues,
      Mutable.allocateBuffer, Except.map]
  · rfl
  · simp [potential, heapPotential, objectPotential]

/-- A slice replacement updates the existing buffer, including through aliases. -/
theorem buffer_slice_operation (heap : Heap) (address : Nat) (bytes replacement updated : List UInt8)
    (lower upper stride : Value)
    (found : heap[address]? = some (.bytearray bytes))
    (evaluated : Mutable.setSlice (.ref address) lower upper stride (.scalar (.bytes replacement)) heap =
      some (.ok (.scalar .none), heap.set address (.bytearray updated)))
    (priced : BufferWork.slice arithmetic bytes.length lower upper stride replacement = some work) :
    Reaches (globals := globals) arithmetic module anchors
      ⟨.operation (.setSlice (.scalar (.bytes replacement))) [.ref address, lower, upper, stride], stack, heap⟩
      (work + 1) ⟨.value (.scalar .none), stack, heap.set address (.bytearray updated)⟩ := by
  apply RuntimeCost.Amortized.Reaches.next (amount := work + 1)
  · simp [step, result, run, primitive, evaluated]
  · simp [charge, operation, BufferWork.operation, found, priced]
  · have equal := heapPotential_set heap address (.bytearray bytes) (.bytearray updated) found
    simpa only [potential, objectPotential, Nat.add_zero] using
      Nat.add_le_add_left (Nat.le_of_eq equal) (work + 1)

theorem ArgumentsIn.reaches {completed : List Value}
    (evaluated : ArgumentsIn (globals := globals) arithmetic module env completed.length expressions heap budget values finalHeap)
    (op : Operation) (anchors : Nat) (stack : List Frame) :
    Reaches (globals := globals) arithmetic module anchors (argumentsState op env completed expressions stack heap) budget
      ⟨.operation op (completed ++ values), stack, finalHeap⟩ := by
  generalize countEq : completed.length = count at evaluated
  induction evaluated generalizing completed with
  | @nil count heap globals => simpa [argumentsState] using
      (RuntimeCost.Amortized.Reaches.refl : Reaches (globals := globals) arithmetic module anchors
        ⟨.operation op completed, stack, _⟩ 0 ⟨.operation op completed, stack, _⟩)
  | @cons expression heap ca value middle globals count expressions cb values finalHeap first rest ih =>
      subst count
      have next : Reaches (globals := globals) arithmetic module anchors
          ⟨.value value, .arguments op completed expressions env :: stack, middle⟩ (completed.length + 1)
          (argumentsState op env (completed ++ [value]) expressions stack middle) :=
        advance rfl rfl (by cases expressions <;> rfl)
      have tail := ih (completed := completed ++ [value]) (by simp)
      simpa only [argumentsState, List.append_assoc, List.singleton_append] using
        ((first anchors (.arguments op completed expressions env :: stack)).trans next).trans tail

namespace EvaluatesIn

theorem buffer_subscript (ordinary : ∀ a b c, index ≠ .slice a b c)
    (receiver : EvaluatesIn (globals := globals) arithmetic module env base heap ca (.ref address) middle)
    (position : EvaluatesIn (globals := globals) arithmetic module env index middle cb (.scalar (.int offset)) afterIndex)
    (found : afterIndex[address]? = some (.bytearray bytes))
    (evaluated : Mutable.getItem (.ref address) (.scalar (.int offset)) afterIndex =
      some (.ok answer, afterIndex)) :
    EvaluatesIn (globals := globals) arithmetic module env (.subscript base index) heap
      (ca + cb + integer arithmetic offset + integer arithmetic bytes.length + 6) answer afterIndex := by
  intro anchors stack
  have initial : Reaches (globals := globals) arithmetic module anchors
      ⟨.expr (.subscript base index) env, stack, heap⟩ 1
      (argumentsState .subscript env [] [base, index] stack heap) :=
    advance (by cases index <;> simp_all [step, argumentsState]) rfl rfl
  have args := (ArgumentsIn.cons receiver (ArgumentsIn.cons position ArgumentsIn.nil)).reaches
    (completed := []) .subscript anchors stack
  have last : Reaches (globals := globals) arithmetic module anchors
      ⟨.operation .subscript [.ref address, .scalar (.int offset)], stack, afterIndex⟩
      (integer arithmetic offset + integer arithmetic bytes.length + 2)
      ⟨.value answer, stack, afterIndex⟩ :=
    advance (by simp [step, primitive, result, run, evaluated])
      (by simp [charge, operation, BufferWork.operation, scalarNumber, found]) rfl
  exact ((initial.trans args).trans last).mono (by simp; omega)

end EvaluatesIn

namespace BlockContinuesIn

theorem buffer_setSlice
    (rhs : EvaluatesIn (globals := globals) arithmetic module env expression heap cr (.scalar (.bytes replacement)) afterRhs)
    (args : ArgumentsIn (globals := globals) arithmetic module env 0
      [base, lower.getD (.constant .none), upper.getD (.constant .none), stride.getD (.constant .none)]
      afterRhs ca [.ref address, first, last, stepValue] afterArgs)
    (found : afterArgs[address]? = some (.bytearray bytes))
    (evaluated : Mutable.setSlice (.ref address) first last stepValue (.scalar (.bytes replacement)) afterArgs =
      some (.ok (.scalar .none), afterArgs.set address (.bytearray updated)))
    (priced : BufferWork.slice arithmetic bytes.length first last stepValue replacement = some work) :
    BlockContinuesIn (globals := globals) arithmetic module env [.assign [.subscript base (.slice lower upper stride)] expression]
      heap (cr + ca + work + 4) env (afterArgs.set address (.bytearray updated)) := by
  intro following anchors stack
  have initial : Reaches (globals := globals) arithmetic module anchors
      ⟨.block ([.assign [.subscript base (.slice lower upper stride)] expression] ++ following) env, stack, heap⟩ 1
      ⟨.expr expression env, .assignSlice base (lower.getD (.constant .none))
        (upper.getD (.constant .none)) (stride.getD (.constant .none)) following env :: stack, heap⟩ :=
    advance rfl rfl rfl
  have ready : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar (.bytes replacement)), .assignSlice base (lower.getD (.constant .none))
        (upper.getD (.constant .none)) (stride.getD (.constant .none)) following env :: stack, afterRhs⟩ 1
      (argumentsState (.setSlice (.scalar (.bytes replacement))) env []
        [base, lower.getD (.constant .none), upper.getD (.constant .none), stride.getD (.constant .none)]
        (.discard following env :: stack) afterRhs) := advance rfl rfl rfl
  have arguments := args.reaches (completed := []) (.setSlice (.scalar (.bytes replacement))) anchors
    (.discard following env :: stack)
  have write := buffer_slice_operation (globals := globals) afterArgs address bytes replacement updated first last stepValue
    (module := module) (anchors := anchors) (stack := .discard following env :: stack) found evaluated priced
  have finish : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar .none), .discard following env :: stack, afterArgs.set address (.bytearray updated)⟩ 1
      ⟨.block following env, stack, afterArgs.set address (.bytearray updated)⟩ := advance rfl rfl rfl
  simpa only [List.nil_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    ((((initial.trans (rhs anchors _)).trans ready).trans arguments).trans write).trans finish

end BlockContinuesIn
end FormalSW.PyAst.HeapCalls.Runtime
