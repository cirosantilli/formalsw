import lang.py.FormalSW.HeapCallsCost

/-! Transition-count rules for list operations and returning control flow.
Collection traversals inside a heap primitive are atomic in these rules. -/
namespace FormalSW.PyAst.HeapCalls.Cost.Lists
open Mutable

/-- List construction charges argument evaluation and the allocation transition. -/
theorem list (arguments : EvaluatesIn.Arguments module env expressions heap cost values finalHeap) :
    EvaluatesIn module env (.list expressions) heap (cost + 2) (.ref finalHeap.length)
      (finalHeap ++ [.list values]) := by
  intro anchors stack
  exact .next rfl ((EvaluatesIn.arguments_reach arguments .list [] anchors stack).trans
    (.next (by simp [step, result, run, primitive, Mutable.allocate, Except.map]) .refl))

theorem append (receiver : EvaluatesIn module env base heap cr (.ref address) middle)
    (found : middle[address]? = some (.list old))
    (item : EvaluatesIn module env expression middle ci value afterItem)
    (items : afterItem[address]? = some (.list current)) :
    EvaluatesIn module env (.call (.attribute base "append") [expression]) heap
      (cr + (ci + 3) + 1) (.scalar .none) (afterItem.set address (.list (current ++ [value]))) := by
  intro anchors stack
  refine .next rfl ((receiver anchors _).trans ?_)
  refine .next (following := ⟨.expr expression env, .arguments (.append address) [] [] env :: stack, middle⟩)
    (by simp [step, run, Mutable.appendReceiver, found, argumentsState]) ?_
  exact (item anchors _).trans (.next (following := ⟨.operation (.append address) [value], stack, afterItem⟩) rfl
    (.next (by simp [step, result, run, primitive, Mutable.appendItem, items, Except.map]) .refl))

theorem reversed (evaluated : EvaluatesIn module env expression heap cost (.ref address) middle)
    (found : middle[address]? = some (.list items)) :
    EvaluatesIn module env (.reversedList expression) heap (cost + 3) (.ref middle.length)
      (middle ++ [.list items.reverse]) := by
  intro anchors stack
  have all := ReachesIn.next (step := step module anchors)
    (state := ⟨.expr (.reversedList expression) env, stack, heap⟩) rfl
    ((EvaluatesIn.arguments_reach (.cons evaluated .nil) .reversedList [] anchors stack).trans
      (.next (following := ⟨.value (.ref middle.length), stack, middle ++ [.list items.reverse]⟩)
        (by simp [step, result, run, primitive, Mutable.sequence, found, Mutable.allocate, Except.map]) .refl))
  simpa [Nat.add_assoc] using all

theorem branch (evaluated : EvaluatesIn module env condition heap cc value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockReturnsIn module env ((if flag then yes else no) ++ following) middle cb answer finalHeap) :
    BlockReturnsIn module env (.ifThen condition yes no :: following) heap (cc + cb + 2) answer finalHeap := by
  intro anchors stack
  have all := ReachesIn.next (step := step module anchors)
    (state := ⟨.block (.ifThen condition yes no :: following) env, stack, heap⟩) rfl
    ((evaluated anchors _).trans (.next (by simp [step, HeapCalls.run, truth]) (rest anchors stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

theorem whileLoop (evaluated : EvaluatesIn module env condition heap cc value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockReturnsIn module env
      ((if flag then body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)] else otherwise) ++ following)
      middle cb answer finalHeap) :
    BlockReturnsIn module env (.whileDo condition body otherwise :: following) heap (cc + cb + 2) answer finalHeap := by
  intro anchors stack
  have all := ReachesIn.next (step := step module anchors)
    (state := ⟨.block (.whileDo condition body otherwise :: following) env, stack, heap⟩) rfl
    ((evaluated anchors _).trans (.next (by simp [step, HeapCalls.run, truth]) (rest anchors stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

end FormalSW.PyAst.HeapCalls.Cost.Lists
