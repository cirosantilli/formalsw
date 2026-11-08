import lang.py.FormalSW.HeapRuntimeCostLists

namespace FormalSW.PyAst.HeapCalls.Runtime
open PrimitiveWork

def BlockContinuesIn (arithmetic : Arithmetic) (module : Module) (env : Env) (body : List Stmt)
    (heap : Heap) (budget : Nat) (finalEnv : Env) (finalHeap : Heap) : Prop :=
  ∀ following anchors stack, Reaches arithmetic module anchors
    ⟨.block (body ++ following) env, stack, heap⟩ budget ⟨.block following finalEnv, stack, finalHeap⟩

def BlockReturnsIn (arithmetic : Arithmetic) (module : Module) (env : Env) (body : List Stmt)
    (heap : Heap) (budget : Nat) (value : Value) (finalHeap : Heap) : Prop :=
  ∀ anchors stack, Reaches arithmetic module anchors
    ⟨.block body env, stack, heap⟩ budget ⟨.value value, stack, finalHeap⟩

def ReturnsIn (arithmetic : Arithmetic) (module : Module) (name : String) (values : List Value)
    (heap : Heap) (budget : Nat) (value : Value) (finalHeap : Heap) : Prop :=
  ∀ anchors stack, Reaches arithmetic module anchors
    ⟨.operation (.call name) values, stack, heap⟩ budget ⟨.value value, stack, finalHeap⟩

namespace EvaluatesIn

theorem empty_list : EvaluatesIn arithmetic module env (.list []) heap 3 (.ref heap.length)
    (heap ++ [.list []]) := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors ⟨.expr (.list []) env, stack, heap⟩ 1
      ⟨.operation .list [], stack, heap⟩ := advance rfl rfl rfl
  exact initial.trans (list_operation heap [])

theorem compare (left : EvaluatesIn arithmetic module env a heap ca av middle)
    (right : EvaluatesIn arithmetic module env b middle cb bv afterRight)
    (evaluated : HeapCalls.compare op av bv afterRight = some (.ok value, afterRight))
    (priced : comparison arithmetic afterRight op av bv = some work) :
    EvaluatesIn arithmetic module env (.compare a [(op, b)]) heap (ca + cb + work + 3) value afterRight := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.compare a [(op, b)]) env, stack, heap⟩ 1
      ⟨.expr a env, .compareLeft op b env :: stack, heap⟩ := advance rfl rfl rfl
  have next : Reaches arithmetic module anchors ⟨.value av, .compareLeft op b env :: stack, middle⟩ 1
      ⟨.expr b env, .compareRight op av :: stack, middle⟩ := advance rfl rfl rfl
  have last : Reaches arithmetic module anchors
      ⟨.value bv, .compareRight op av :: stack, afterRight⟩ (work + 1)
      ⟨.value value, stack, afterRight⟩ :=
    advance (by simp [step, result, run, evaluated]) (by simp [charge, priced]) rfl
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (((initial.trans (left anchors _)).trans next).trans (right anchors _)).trans last

end EvaluatesIn

namespace BlockContinuesIn

theorem mono (run : BlockContinuesIn arithmetic module env body heap small finalEnv finalHeap)
    (larger : small ≤ large) : BlockContinuesIn arithmetic module env body heap large finalEnv finalHeap :=
  fun following anchors stack => (run following anchors stack).mono larger

theorem nil : BlockContinuesIn arithmetic module env [] heap 0 env heap := fun _ _ _ => .refl

theorem append (first : BlockContinuesIn arithmetic module env body heap ca middleEnv middleHeap)
    (second : BlockContinuesIn arithmetic module middleEnv rest middleHeap cb finalEnv finalHeap) :
    BlockContinuesIn arithmetic module env (body ++ rest) heap (ca + cb) finalEnv finalHeap := by
  intro following anchors stack
  simpa only [List.append_assoc] using
    (first (rest ++ following) anchors stack).trans (second following anchors stack)

theorem assign (evaluated : EvaluatesIn arithmetic module env expression heap cost value finalHeap) :
    BlockContinuesIn arithmetic module env [.assign [.name name] expression] heap
      (cost + 2) (setLocal env name value) finalHeap := by
  intro following anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.block ([.assign [.name name] expression] ++ following) env, stack, heap⟩ 1
      ⟨.expr expression env, .assign name following env :: stack, heap⟩ := advance rfl rfl rfl
  have last : Reaches arithmetic module anchors ⟨.value value, .assign name following env :: stack, finalHeap⟩ 1
      ⟨.block following (setLocal env name value), stack, finalHeap⟩ := advance rfl rfl rfl
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (initial.trans (evaluated anchors _)).trans last

theorem discard (evaluated : EvaluatesIn arithmetic module env expression heap cost value finalHeap) :
    BlockContinuesIn arithmetic module env [.expr expression] heap (cost + 2) env finalHeap := by
  intro following anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.block ([.expr expression] ++ following) env, stack, heap⟩ 1
      ⟨.expr expression env, .discard following env :: stack, heap⟩ := advance rfl rfl rfl
  have last : Reaches arithmetic module anchors ⟨.value value, .discard following env :: stack, finalHeap⟩ 1
      ⟨.block following env, stack, finalHeap⟩ := advance rfl rfl rfl
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (initial.trans (evaluated anchors _)).trans last

theorem augAssign (lookup : env name = some (.scalar left))
    (evaluated : EvaluatesIn arithmetic module env expression heap cost (.scalar right) middle)
    (operation : inplace op (.scalar left) (.scalar right) middle = some (.ok value, middle))
    (priced : PrimitiveWork.binary arithmetic op left right = some work) :
    BlockContinuesIn arithmetic module env [.augAssign (.name name) op expression] heap
      (cost + work + 5) (setLocal env name value) middle := by
  intro following anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.block ([.augAssign (.name name) op expression] ++ following) env, stack, heap⟩ 1
      ⟨.expr (.name name) env, .binaryLeft op expression env true :: .assign name following env :: stack, heap⟩ :=
    advance rfl rfl rfl
  have loaded := EvaluatesIn.lookup (arithmetic := arithmetic) (module := module) (heap := heap)
    lookup anchors (.binaryLeft op expression env true :: .assign name following env :: stack)
  have next : Reaches arithmetic module anchors
      ⟨.value (.scalar left), .binaryLeft op expression env true :: .assign name following env :: stack, heap⟩ 1
      ⟨.expr expression env, .binaryRight op (.scalar left) true :: .assign name following env :: stack, heap⟩ :=
    advance rfl rfl rfl
  have arithmeticRun : Reaches arithmetic module anchors
      ⟨.value (.scalar right), .binaryRight op (.scalar left) true :: .assign name following env :: stack, middle⟩
      (work + 1) ⟨.value value, .assign name following env :: stack, middle⟩ :=
    advance (by simp [step, result, run, operation]) (by simp [charge, priced]) rfl
  have last : Reaches arithmetic module anchors ⟨.value value, .assign name following env :: stack, middle⟩ 1
      ⟨.block following (setLocal env name value), stack, middle⟩ := advance rfl rfl rfl
  have total : 1 + 1 + 1 + cost + (work + 1) + 1 = cost + work + 5 := by omega
  simpa only [total] using
    ((((initial.trans loaded).trans next).trans (evaluated anchors _)).trans arithmeticRun).trans last

theorem returns (first : BlockContinuesIn arithmetic module env body heap ca middleEnv middleHeap)
    (rest : BlockReturnsIn arithmetic module middleEnv following middleHeap cb answer finalHeap) :
    BlockReturnsIn arithmetic module env (body ++ following) heap (ca + cb) answer finalHeap :=
  fun anchors stack => (first following anchors stack).trans (rest anchors stack)

end BlockContinuesIn

namespace BlockReturnsIn

theorem mono (run : BlockReturnsIn arithmetic module env body heap small value finalHeap)
    (larger : small ≤ large) : BlockReturnsIn arithmetic module env body heap large value finalHeap :=
  fun anchors stack => (run anchors stack).mono larger

theorem return_value (evaluated : EvaluatesIn arithmetic module env expression heap cost value finalHeap) :
    BlockReturnsIn arithmetic module env (.return expression :: following) heap (cost + 1) value finalHeap := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.block (.return expression :: following) env, stack, heap⟩ 1
      ⟨.expr expression env, stack, heap⟩ := advance rfl rfl rfl
  simpa only [Nat.add_comm] using initial.trans (evaluated anchors stack)

theorem assign (evaluated : EvaluatesIn arithmetic module env expression heap ca value middle)
    (rest : BlockReturnsIn arithmetic module (setLocal env name value) following middle cb answer finalHeap) :
    BlockReturnsIn arithmetic module env (.assign [.name name] expression :: following) heap
      (ca + cb + 2) answer finalHeap := by
  have run := (BlockContinuesIn.assign (name := name) evaluated).returns rest
  simpa only [List.singleton_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem branch (evaluated : EvaluatesIn arithmetic module env condition heap cc (.scalar value) middle)
    (test : Mutable.truth (.scalar value) middle = some (.ok flag, middle))
    (rest : BlockReturnsIn arithmetic module env ((if flag then yes else no) ++ following)
      middle cb answer finalHeap) :
    BlockReturnsIn arithmetic module env (.ifThen condition yes no :: following) heap
      (cc + cb + 2) answer finalHeap := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.block (.ifThen condition yes no :: following) env, stack, heap⟩ 1
      ⟨.expr condition env, .branch yes no following env :: stack, heap⟩ := advance rfl rfl rfl
  have next : Reaches arithmetic module anchors
      ⟨.value (.scalar value), .branch yes no following env :: stack, middle⟩ 1
      ⟨.block ((if flag then yes else no) ++ following) env, stack, middle⟩ :=
    advance (by simp [step, run, test]) rfl rfl
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    ((initial.trans (evaluated anchors _)).trans next).trans (rest anchors stack)

theorem while_loop (evaluated : EvaluatesIn arithmetic module env condition heap cc (.scalar value) middle)
    (test : Mutable.truth (.scalar value) middle = some (.ok flag, middle))
    (rest : BlockReturnsIn arithmetic module env
      ((if flag then body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)] else otherwise) ++ following)
      middle cb answer finalHeap) :
    BlockReturnsIn arithmetic module env (.whileDo condition body otherwise :: following) heap
      (cc + cb + 2) answer finalHeap := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.block (.whileDo condition body otherwise :: following) env, stack, heap⟩ 1
      ⟨.expr condition env, .branch (body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)])
        otherwise following env :: stack, heap⟩ := advance rfl rfl rfl
  have next : Reaches arithmetic module anchors
      ⟨.value (.scalar value), .branch (body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)])
        otherwise following env :: stack, middle⟩ 1
      ⟨.block ((if flag then body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)] else otherwise) ++ following)
        env, stack, middle⟩ := advance (by simp [step, run, test]) rfl rfl
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    ((initial.trans (evaluated anchors _)).trans next).trans (rest anchors stack)

theorem function (found : findFunctionIn module.body name = some (args, body))
    (arity : completeArguments args values = some completed)
    (evaluated : BlockReturnsIn arithmetic module (functionEnv args body completed []) (executableBody body)
      heap budget value finalHeap) :
    ReturnsIn arithmetic module name values heap (values.length + args.length + 1 + budget) value finalHeap := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors ⟨.operation (.call name) values, stack, heap⟩
      (values.length + args.length + 1)
      ⟨.block (executableBody body) (functionEnv args body completed []), stack, heap⟩ :=
    advance (by simp [step, found, arity]) (by simp [charge, found]) rfl
  exact initial.trans (evaluated anchors stack)

end BlockReturnsIn
end FormalSW.PyAst.HeapCalls.Runtime
