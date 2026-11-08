import lang.py.FormalSW.HeapRuntimeCostPrimitives

namespace FormalSW.PyAst.HeapCalls.Runtime

theorem EvaluatesIn.empty_set :
    EvaluatesIn arithmetic module env (.builtinCall .set []) heap 3 (.ref heap.length)
      (heap ++ [.set []]) := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.expr (.builtinCall .set []) env, stack, heap⟩ 1
      ⟨.operation (.builtin .set) [], stack, heap⟩ := advance rfl rfl rfl
  have allocated : Reaches arithmetic module anchors
      ⟨.operation (.builtin .set) [], stack, heap⟩ 2
      ⟨.value (.ref heap.length), stack, heap ++ [.set []]⟩ := by
    apply RuntimeCost.Amortized.Reaches.next (amount := 2)
    · simp [step, result, run, primitive, Mutable.allocateSet, Except.map]
    · rfl
    · simp [potential, heapPotential, objectPotential]
  exact first.trans allocated

theorem EvaluatesIn.set_add
    (receiver : EvaluatesIn arithmetic module env base heap ca (.ref address) middle)
    (found : middle[address]? = some (.set old))
    (item : EvaluatesIn arithmetic module env expression middle cb (.scalar value) afterItem)
    (items : afterItem[address]? = some (.set current)) :
    EvaluatesIn arithmetic module env (.call (.attribute base "add") [expression]) heap
      (ca + cb + SetWork.insert .collisionChain arithmetic current value + 4) (.scalar .none)
      (afterItem.set address (.set (ScalarSet.insert current value))) := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.expr (.call (.attribute base "add") [expression]) env, stack, heap⟩ 1
      ⟨.expr base env, .addReceiver expression env :: stack, heap⟩ := advance rfl rfl rfl
  have ready : Reaches arithmetic module anchors
      ⟨.value (.ref address), .addReceiver expression env :: stack, middle⟩ 1
      ⟨.expr expression env, .arguments (.add address) [] [] env :: stack, middle⟩ :=
    advance (by simp [step, run, Mutable.addReceiver, found, argumentsState])
      (by simp [charge, found]) rfl
  have argument : Reaches arithmetic module anchors
      ⟨.value (.scalar value), .arguments (.add address) [] [] env :: stack, afterItem⟩ 1
      ⟨.operation (.add address) [.scalar value], stack, afterItem⟩ := advance rfl rfl rfl
  have inserted : Reaches arithmetic module anchors
      ⟨.operation (.add address) [.scalar value], stack, afterItem⟩
      (SetWork.insert .collisionChain arithmetic current value + 1)
      ⟨.value (.scalar .none), stack, afterItem.set address (.set (ScalarSet.insert current value))⟩ := by
    apply RuntimeCost.Amortized.Reaches.next
      (amount := SetWork.insert .collisionChain arithmetic current value + 1)
    · simp [step, result, run, primitive, Mutable.addItem, items, Except.map]
    · simp [charge, operation, SetWork.operation, items]
    · have unchanged := heapPotential_set afterItem address (.set current)
        (.set (ScalarSet.insert current value)) items
      simpa only [potential, objectPotential, Nat.add_zero] using
        Nat.add_le_add_left (Nat.le_of_eq unchanged)
          (SetWork.insert .collisionChain arithmetic current value + 1)
  exact (((((first.trans (receiver anchors _)).trans ready).trans (item anchors _)).trans argument).trans inserted).mono
    (by omega)

theorem EvaluatesIn.set_maximum
    (argument : EvaluatesIn arithmetic module env expression heap ca (.ref address) middle)
    (found : middle[address]? = some (.set items))
    (evaluated : ScalarSet.maximum items = .ok answer) :
    EvaluatesIn arithmetic module env (.builtinCall .max [expression]) heap
      (ca + SetWork.extremum arithmetic items + 3) (.scalar answer) middle := by
  apply EvaluatesIn.builtin_single (by intro h; cases h) (by intro h; cases h) argument
  · have readScalars : (items.mapM (fun value => pure value) : Mutable.Eval (List Constant)) = pure items := by
      simpa using (List.mapM_pure (m := Mutable.Eval) (l := items) (f := id))
    simp [primitive, found, List.mapM_map, Function.comp_def, readScalars, scalarResult, evaluated]
  · simp [operation, SetWork.operation, found]

theorem EvaluatesIn.set_conditional
    (condition : EvaluatesIn arithmetic module env test heap ct (.ref address) middle)
    (found : middle[address]? = some (.set items))
    (tested : Mutable.truth (.ref address) middle = some (.ok flag, middle))
    (branch : EvaluatesIn arithmetic module env (if flag then yes else no) middle cb answer finalHeap) :
    EvaluatesIn arithmetic module env (.ifExp test yes no) heap (ct + cb + 2) answer finalHeap := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.expr (.ifExp test yes no) env, stack, heap⟩ 1
      ⟨.expr test env, .conditional yes no env :: stack, heap⟩ := advance rfl rfl rfl
  have chosen : Reaches arithmetic module anchors
      ⟨.value (.ref address), .conditional yes no env :: stack, middle⟩ 1
      ⟨.expr (if flag then yes else no) env, stack, middle⟩ :=
    advance (by simp [step, run, tested]) (by simp [charge, truth, found]) rfl
  exact (((first.trans (condition anchors _)).trans chosen).trans (branch anchors stack)).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime
