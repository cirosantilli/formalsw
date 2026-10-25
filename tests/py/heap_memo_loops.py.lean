import «.formalsw».tests.py.«heap_memo_loops.py.ast»
import lang.py.FormalSW.HeapMemoCallRules

namespace tests.py.heap_memo_loops
open FormalSW.PyAst FormalSW.PyAst.HeapMemoCalls
private abbrev program := HeapMemoLoopsAst.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)

/-- Successful cached results are scalars, even though misses allocate a list. -/
private def spec (_heap : Mutable.Heap) (key : MemoCalls.Key) (value : Mutable.Value) : Prop :=
  ∃ n, key = ⟨"seed", [n]⟩ ∧ value = number n

private theorem preserves (before after : Mutable.Heap) : Cache.Preserves spec before after :=
  fun _ valid => valid

private theorem list_evaluates
    (arguments : Evaluates.Arguments program spec env expressions heap values middle) :
    Evaluates program spec env (.list expressions) heap (.ref middle.length)
      (middle ++ [.list values]) :=
  Evaluates.list arguments (preserves middle _)

private theorem found_append {heap : Mutable.Heap} {address : Nat} {object : Mutable.Object}
    (found : heap[address]? = some object) (extra : Mutable.Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem list_sequence {heap : Mutable.Heap} {address : Nat} {items : List Mutable.Value}
    (found : heap[address]? = some (.list items)) :
    Mutable.sequence (.ref address) heap = some (.ok items, heap) := by
  simp [Mutable.sequence, found]

private theorem seed.result (n : Int) (heap : Mutable.Heap) :
    ReturnsRel program spec "seed" [number n] heap
      (fun value after => value = number n ∧ ∃ extra, after = heap ++ extra) := by
  apply BlockReturnsRel.memoized_function (values := [n]) (by decide) rfl rfl
  · apply BlockReturnsRel.return_value
    apply (Evaluates.subscript (value := number n)
      (finalHeap := heap ++ [.list [number n]])
      (ordinary := by intro x y z equal; cases equal)
      (list_evaluates (.cons (Evaluates.lookup (value := number n) rfl) .nil)) Evaluates.constant
      (by simp [Mutable.getItem, Mutable.index, Except.map])
      (preserves _ _)).rel.consequence
    rintro value after ⟨equalValue, equalHeap⟩
    subst value
    subst after
    exact ⟨⟨rfl, [.list [number n]], rfl⟩, n, rfl, rfl⟩
  · rintro value ⟨other, equal, same⟩
    have equalNumbers : n = other := by simpa [MemoCalls.Key.mk.injEq] using equal
    subst other
    exact ⟨same, [], by simp⟩

private theorem seed_evaluates (n : Int) (heap : Mutable.Heap)
    (argument : Evaluates program spec env expression heap (number n) heap) :
    EvaluatesRel program spec env (.call (.name "seed") [expression]) heap
      (fun value after => value = number n ∧ ∃ extra, after = heap ++ extra) := by
  apply EvaluatesRel.call (ArgumentsRel.fixed (.cons argument .nil))
  rintro values middle ⟨equalValues, equalHeap⟩
  subst values
  subst middle
  exact seed.result n heap

private abbrev incrementCondition : Expr :=
  .compare (.name "i") [(.lt, .binOp (.name "n") .add (.constant (.int 1)))]
private abbrev incrementBody : List Stmt :=
  [.augAssign (.name "i") .add (.call (.name "seed") [.constant (.int 1)])]
private abbrev incrementTail : List Stmt :=
  [.whileDo incrementCondition incrementBody [], .return (.name "i")]

private theorem increment_done (n : Int) (env : Mutable.Env) (heap : Mutable.Heap)
    (getN : env "n" = some (number n)) (getI : env "i" = some (number (n + 1))) :
    BlockReturnsRel program spec env incrementTail heap
      (fun value _ => value = number (n + 1)) := by
  apply BlockReturnsRel.while_loop
  · apply (Evaluates.compare (Evaluates.lookup getI)
      (Evaluates.binary (Evaluates.lookup getN) Evaluates.constant rfl)
      (value := .scalar (.bool false)) ?_).rel
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  · rintro value middle ⟨equalValue, equalHeap⟩
    subst value
    subst middle
    refine ⟨false, rfl, ?_⟩
    exact BlockReturnsRel.return_value (EvaluatesRel.lookup getI rfl)

private theorem increment_once (n : Int) (env : Mutable.Env) (heap : Mutable.Heap)
    (getN : env "n" = some (number n)) (getI : env "i" = some (number n)) :
    BlockReturnsRel program spec env incrementTail heap
      (fun value _ => value = number (n + 1)) := by
  apply BlockReturnsRel.while_loop
  · apply (Evaluates.compare (Evaluates.lookup getI)
      (Evaluates.binary (Evaluates.lookup getN) Evaluates.constant rfl)
      (value := .scalar (.bool true)) ?_).rel
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    omega
  · rintro value middle ⟨equalValue, equalHeap⟩
    subst value
    subst middle
    refine ⟨true, rfl, ?_⟩
    apply BlockReturnsRel.augAssign getI (seed_evaluates 1 heap Evaluates.constant)
    rintro right after ⟨rfl, extra, rfl⟩
    refine ⟨number (n + 1), heap ++ extra, rfl, Cache.Preserves.refl, ?_⟩
    simpa [incrementBody, incrementTail, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt] using
      increment_done n (HeapCalls.setLocal env "i" (number (n + 1))) (heap ++ extra)
        (by simpa [HeapCalls.setLocal] using getN) (by simp [HeapCalls.setLocal])

/-- The while loop runs once for every signed input and executes the cached RHS. -/
theorem increment.result (n : Int) (heap : Mutable.Heap) :
    ReturnsRel program spec "increment" [number n] heap
      (fun value _ => value = number (n + 1)) := by
  apply BlockReturnsRel.function (by decide) rfl rfl
  apply BlockReturnsRel.assign (Evaluates.lookup (value := number n) rfl).rel
  rintro value middle ⟨equalValue, equalHeap⟩
  subst value
  subst middle
  apply increment_once n
  · rfl
  · rfl

private abbrev sumElement : Expr := .call (.name "seed") [.name "x"]
private abbrev sumRow : List Stmt :=
  [.assign [.name HeapCalls.sumAccumulator] (.binOp (.name HeapCalls.sumAccumulator) .add sumElement)]
private abbrev sumTail (address position : Nat) : List Stmt :=
  [.sequenceStepLoop "x" (.ref address) position sumRow [], .return (.name HeapCalls.sumAccumulator)]

private theorem add_seed (env : Mutable.Env) (heap : Mutable.Heap) (total value : Int)
    (getTotal : env HeapCalls.sumAccumulator = some (number total))
    (getX : env "x" = some (number value)) :
    EvaluatesRel program spec env (.binOp (.name HeapCalls.sumAccumulator) .add sumElement) heap
      (fun answer after => answer = number (total + value) ∧ ∃ extra, after = heap ++ extra) := by
  apply EvaluatesRel.binary
    (rightPost := fun _ _ answer after => answer = number value ∧ ∃ extra, after = heap ++ extra)
    (Evaluates.lookup getTotal).rel
  · rintro left middle ⟨equalLeft, equalHeap⟩
    subst left
    subst middle
    exact seed_evaluates value heap (Evaluates.lookup getX)
  · rintro left middle right after ⟨equalLeft, equalHeap⟩ ⟨equalRight, extra, equalAfter⟩
    subst left
    subst middle
    subst right
    subst after
    exact ⟨number (total + value), heap ++ extra, rfl, Cache.Preserves.refl, rfl, extra, rfl⟩

private theorem sum_step (env : Mutable.Env) (heap : Mutable.Heap) (address position : Nat)
    (items : List Mutable.Value) (value total answer : Int)
    (found : heap[address]? = some (.list items)) (item : items[position]? = some (number value))
    (getTotal : env HeapCalls.sumAccumulator = some (number total))
    (continued : ∀ extra, BlockReturnsRel program spec
      (HeapCalls.setLocal (HeapCalls.setLocal env "x" (number value)) HeapCalls.sumAccumulator (number (total + value)))
      (sumTail address (position + 1)) (heap ++ extra) (fun result _ => result = number answer)) :
    BlockReturnsRel program spec env (sumTail address position) heap (fun result _ => result = number answer) := by
  apply BlockReturnsRel.sequence_step (items := items)
    (by simp [HeapCalls.sequenceValue, Mutable.sequence, found]) item
  apply BlockReturnsRel.assign
    (add_seed _ heap total value (by simpa [HeapCalls.setLocal] using getTotal) (by simp [HeapCalls.setLocal]))
  rintro result after ⟨rfl, extra, rfl⟩
  simpa [sumTail, sumRow, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt] using continued extra

private theorem sum_two (n : Int) (env : Mutable.Env) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list [number n, number (n + 1)]))
    (getTotal : env HeapCalls.sumAccumulator = some (number 0)) :
    BlockReturnsRel program spec env (sumTail address 0) heap
      (fun value _ => value = number (2 * n + 1)) := by
  apply sum_step env heap address 0 [number n, number (n + 1)] n 0 (2 * n + 1) found rfl getTotal
  intro firstExtra
  apply sum_step _ (heap ++ firstExtra) address 1 [number n, number (n + 1)] (n + 1) n (2 * n + 1)
    (found_append found firstExtra) rfl (by simp [HeapCalls.setLocal, number])
  intro secondExtra
  apply BlockReturnsRel.sequence_done (items := [number n, number (n + 1)])
    (by simpa only [HeapCalls.sequenceValue] using
      list_sequence (found_append (found_append found firstExtra) secondExtra)) rfl
  apply BlockReturnsRel.return_value
  apply EvaluatesRel.lookup (value := number (n + (n + 1))) (by simp [HeapCalls.setLocal, number])
  exact congrArg number (by omega)

/-- Both source elements are consumed in order, allowing each seed call to allocate. -/
theorem sum_seed.result (n : Int) (heap : Mutable.Heap) :
    ReturnsRel program spec "sum_seed" [number n] heap
      (fun value _ => value = number (2 * n + 1)) := by
  apply BlockReturnsRel.function (by decide) rfl rfl
  apply BlockReturnsRel.return_value
  apply EvaluatesRel.sum_generator_sequence
    (iterablePost := fun value after => value = .ref heap.length ∧
      after = heap ++ [.list [number n, number (n + 1)]])
    (startPost := fun _ middle value after => value = number 0 ∧ after = middle)
  · exact (list_evaluates (.cons (Evaluates.lookup (value := number n) rfl) (.cons
      (Evaluates.binary (Evaluates.lookup (value := number n) rfl) Evaluates.constant rfl) .nil))).rel
  · intro bounds equal
    cases equal
  · rintro source middle ⟨rfl, rfl⟩
    exact ⟨[number n, number (n + 1)], by simp [Mutable.sequence]⟩
  · intro source middle _
    exact EvaluatesRel.constant ⟨rfl, rfl⟩
  · rintro source middle initial afterStart ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    apply sum_two n _ _ heap.length (by simp)
    rfl

theorem increment.«Returns» (n : Int) :
    (HeapMemoCalls.scalarFunction program "increment" [.int n]).Returns :=
  ReturnsRel.scalar_returns ((increment.result n []).consequence (by intro value after same; exact ⟨same, True.intro⟩))

theorem increment.«Supported» (n : Int) :
    (HeapMemoCalls.scalarFunction program "increment" [.int n]).Supported :=
  (increment.«Returns» n).supported

theorem sum_seed.«Returns» (n : Int) :
    (HeapMemoCalls.scalarFunction program "sum_seed" [.int n]).Returns :=
  ReturnsRel.scalar_returns ((sum_seed.result n []).consequence (by intro value after same; exact ⟨same, True.intro⟩))

theorem sum_seed.«Supported» (n : Int) :
    (HeapMemoCalls.scalarFunction program "sum_seed" [.int n]).Supported :=
  (sum_seed.«Returns» n).supported

end tests.py.heap_memo_loops
