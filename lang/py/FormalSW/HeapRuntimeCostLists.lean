import lang.py.FormalSW.HeapRuntimeCost

/-! Source-level rules for list runtime costs. Budgets include credits retained
by every allocated list, including unreachable lists and aliased receivers. -/
namespace FormalSW.PyAst.HeapCalls.Runtime
variable {globals : Mutable.Globals}
open PrimitiveWork

abbrev Reaches (arithmetic : Arithmetic) (module : Module) (anchors : Nat)
    (initial : State) (budget : Nat) (final : State) (globals : Mutable.Globals := []) :=
  RuntimeCost.Amortized.Reaches (step (globals := globals) module anchors) (charge arithmetic module)
    potential initial budget final

def EvaluatesIn (arithmetic : Arithmetic) (module : Module) (env : Env) (expression : Expr)
    (heap : Heap) (budget : Nat) (value : Value) (finalHeap : Heap) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, Reaches (globals := globals) arithmetic module anchors
    ⟨.expr expression env, stack, heap⟩ budget ⟨.value value, stack, finalHeap⟩

theorem advance (transition : step (globals := globals) module anchors initial = .next following)
    (measured : charge arithmetic module initial = some amount)
    (unchanged : following.heap = initial.heap) :
    Reaches (globals := globals) arithmetic module anchors initial amount following := by
  apply RuntimeCost.Amortized.Reaches.next
    (step := fun state => step (globals := globals) module anchors state)
    (charge := fun state => charge arithmetic module state) transition measured
  simp only [potential, unchanged]
  omega

theorem heapPotential_allocate (heap : Heap) (items : List Value) :
    heapPotential (heap ++ [.list items]) = heapPotential heap + DynamicArray.potential items.length := by
  simp [heapPotential, objectPotential]

theorem heapPotential_set (heap : Heap) (address : Nat) (old replacement : Mutable.Object)
    (found : heap[address]? = some old) :
    heapPotential (heap.set address replacement) + objectPotential old =
      heapPotential heap + objectPotential replacement := by
  induction heap generalizing address with
  | nil => simp at found
  | cons head tail ih =>
      cases address with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst head
          simp [heapPotential, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      | succ address =>
          have tailFound : tail[address]? = some old := by simpa using found
          have paid := ih address tailFound
          simpa only [heapPotential, List.set_cons_succ, List.map_cons, List.sum_cons,
            Nat.add_assoc] using congrArg (objectPotential head + ·) paid

/-- A resize may be linear in the current length, but four prepaid units cover
the append transition and its contribution to the array potential. -/
theorem append_operation (heap : Heap) (address : Nat) (items : List Value) (value : Value)
    (found : heap[address]? = some (.list items)) :
    Reaches (globals := globals) arithmetic module anchors
      ⟨.operation (.append address) [value], stack, heap⟩ 4
      ⟨.value (.scalar .none), stack, heap.set address (.list (items ++ [value]))⟩ := by
  apply RuntimeCost.Amortized.Reaches.next
    (amount := DynamicArray.append items.length + 1)
  · simp [step, result, run, primitive, Mutable.appendItem, found, Except.map]
  · simp [charge, operation, found]
  · have paid := DynamicArray.append_amortized items.length
    have changed := heapPotential_set heap address (.list items) (.list (items ++ [value])) found
    simp only [objectPotential, List.length_append, List.length_singleton] at changed
    simp only [potential]
    omega

theorem list_operation (heap : Heap) (items : List Value) :
    Reaches (globals := globals) arithmetic module anchors ⟨.operation .list items, stack, heap⟩ (2 * items.length + 2)
      ⟨.value (.ref heap.length), stack, heap ++ [.list items]⟩ := by
  apply RuntimeCost.Amortized.Reaches.next (amount := items.length + 2)
  · simp [step, result, run, primitive, Mutable.allocate, Except.map]
  · rfl
  · have paid := DynamicArray.potential_le items.length
    simp only [potential, heapPotential_allocate]
    omega

theorem reversed_operation (heap : Heap) (address : Nat) (items : List Value)
    (found : heap[address]? = some (.list items)) :
    Reaches (globals := globals) arithmetic module anchors ⟨.operation .reversedList [.ref address], stack, heap⟩
      (2 * items.length + 2) ⟨.value (.ref heap.length), stack, heap ++ [.list items.reverse]⟩ := by
  apply RuntimeCost.Amortized.Reaches.next (amount := items.length + 2)
  · simp [step, result, run, primitive, Mutable.sequence, found, Mutable.allocate, Except.map]
  · simp [charge, operation, sequenceLength, found, sequenceCopy]
  · have paid := DynamicArray.potential_le items.length
    simp only [potential, heapPotential_allocate, List.length_reverse]
    omega

namespace EvaluatesIn

theorem mono (run : EvaluatesIn (globals := globals) arithmetic module env expression heap small value finalHeap)
    (larger : small ≤ large) : EvaluatesIn (globals := globals) arithmetic module env expression heap large value finalHeap :=
  fun anchors stack => (run anchors stack).mono larger

theorem constant : EvaluatesIn (globals := globals) arithmetic module env (.constant value) heap 1 (.scalar value) heap :=
  fun _ _ => advance rfl rfl rfl

theorem lookup (found : env name = some value) :
    EvaluatesIn (globals := globals) arithmetic module env (.name name) heap 1 value heap :=
  fun _ _ => advance (by simp [step, found]) rfl rfl

theorem binary (left : EvaluatesIn (globals := globals) arithmetic module env a heap ca (.scalar av) middle)
    (right : EvaluatesIn (globals := globals) arithmetic module env b middle cb (.scalar bv) afterRight)
    (evaluated : Mutable.binary op (.scalar av) (.scalar bv) afterRight = some (.ok value, afterRight))
    (priced : PrimitiveWork.binary arithmetic op av bv = some work) :
    EvaluatesIn (globals := globals) arithmetic module env (.binOp a op b) heap (ca + cb + work + 3) value afterRight := by
  intro anchors stack
  have initial : Reaches (globals := globals) arithmetic module anchors
      ⟨.expr (.binOp a op b) env, stack, heap⟩ 1
      ⟨.expr a env, .binaryLeft op b env false :: stack, heap⟩ := advance rfl rfl rfl
  have next : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar av), .binaryLeft op b env false :: stack, middle⟩ 1
      ⟨.expr b env, .binaryRight op (.scalar av) false :: stack, middle⟩ := advance rfl rfl rfl
  have last : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar bv), .binaryRight op (.scalar av) false :: stack, afterRight⟩ (work + 1)
      ⟨.value value, stack, afterRight⟩ :=
    advance (by simp [step, result, run, evaluated]) (by simp [charge, priced]) rfl
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (((initial.trans (left anchors _)).trans next).trans (right anchors _)).trans last

theorem append (receiver : EvaluatesIn (globals := globals) arithmetic module env base heap cr (.ref address) middle)
    (found : middle[address]? = some (.list old))
    (item : EvaluatesIn (globals := globals) arithmetic module env expression middle ci value afterItem)
    (items : afterItem[address]? = some (.list current)) :
    EvaluatesIn (globals := globals) arithmetic module env (.call (.attribute base "append") [expression]) heap
      (cr + ci + 7) (.scalar .none) (afterItem.set address (.list (current ++ [value]))) := by
  intro anchors stack
  have initial : Reaches (globals := globals) arithmetic module anchors
      ⟨.expr (.call (.attribute base "append") [expression]) env, stack, heap⟩ 1
      ⟨.expr base env, .appendReceiver expression env :: stack, heap⟩ := advance rfl rfl rfl
  have bound : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.ref address), .appendReceiver expression env :: stack, middle⟩ 1
      ⟨.expr expression env, .arguments (.append address) [] [] env :: stack, middle⟩ :=
    advance (by simp [step, run, Mutable.appendReceiver, found, argumentsState])
      (by simp [charge, found]) rfl
  have argument : Reaches (globals := globals) arithmetic module anchors
      ⟨.value value, .arguments (.append address) [] [] env :: stack, afterItem⟩ 1
      ⟨.operation (.append address) [value], stack, afterItem⟩ := advance rfl rfl rfl
  have last := append_operation (globals := globals) (arithmetic := arithmetic) (module := module) (anchors := anchors)
    (stack := stack) afterItem address current value items
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    ((((initial.trans (receiver anchors _)).trans bound).trans (item anchors _)).trans argument).trans last

theorem reversed (evaluated : EvaluatesIn (globals := globals) arithmetic module env expression heap cost (.ref address) middle)
    (found : middle[address]? = some (.list items)) :
    EvaluatesIn (globals := globals) arithmetic module env (.reversedList expression) heap
      (cost + 2 * items.length + 4) (.ref middle.length) (middle ++ [.list items.reverse]) := by
  intro anchors stack
  have initial : Reaches (globals := globals) arithmetic module anchors
      ⟨.expr (.reversedList expression) env, stack, heap⟩ 1
      ⟨.expr expression env, .arguments .reversedList [] [] env :: stack, heap⟩ := advance rfl rfl rfl
  have argument : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.ref address), .arguments .reversedList [] [] env :: stack, middle⟩ 1
      ⟨.operation .reversedList [.ref address], stack, middle⟩ := advance rfl rfl rfl
  have last := reversed_operation (globals := globals) (arithmetic := arithmetic) (module := module) (anchors := anchors)
    (stack := stack) middle address items found
  have total : 1 + cost + 1 + (2 * items.length + 2) = cost + 2 * items.length + 4 := by omega
  simpa only [total] using ((initial.trans (evaluated anchors _)).trans argument).trans last

end EvaluatesIn
end FormalSW.PyAst.HeapCalls.Runtime
