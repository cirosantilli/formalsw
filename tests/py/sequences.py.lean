import «.formalsw».tests.py.«sequences.py.ast»
import FormalSW

namespace tests.py.sequences
open FormalSW.PyAst
private abbrev program := SequencesAst.module
private abbrev productBody : List Stmt := [.augAssign (.name "p") .mult (.name "x")]
private def ints (xs : List Int) : List Mutable.Value := xs.map fun x => .scalar (.int x)

private def productValue : List Int → Int
  | [] => 1
  | head :: tail => head * productValue tail

/-- A product loop preserves its input heap, including all aliases to that list. -/
private theorem product.loop (remaining : List Int) (before : List Int) (heap : Mutable.Heap)
    (address : Nat) (found : heap[address]? = some (.list (ints (before ++ remaining))))
    (env : HeapCalls.Env) (acc : Int) (hp : env "p" = some (.scalar (.int acc))) :
    HeapCalls.BlockReturns program env
      [.sequenceStepLoop "x" (.ref address) before.length productBody [], .return (.name "p")]
      heap (.scalar (.int (acc * productValue remaining))) heap := by
  induction remaining generalizing before env acc with
  | nil =>
      apply HeapCalls.BlockReturns.sequence_done (items := ints before)
      · simp only [List.append_nil] at found
        simp [HeapCalls.sequenceValue, Mutable.sequence, found]
      · simp [ints]
      · simpa [productValue] using HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup hp)
  | cons value rest ih =>
      apply HeapCalls.BlockReturns.sequence_step (items := ints (before ++ value :: rest)) (value := .scalar (.int value))
      · simp [HeapCalls.sequenceValue, Mutable.sequence, found]
      · simp [ints]
      · apply HeapCalls.BlockReturns.augAssign (by simpa [HeapCalls.setLocal] using hp)
          (HeapCalls.Evaluates.lookup rfl) (middle := heap) (afterOperation := heap) (right := .scalar (.int value))
          (value := .scalar (.int (acc * value)))
        · rfl
        · have next := ih (before ++ [value]) (by simpa [List.append_assoc] using found)
            (HeapCalls.setLocal (HeapCalls.setLocal env "x" (.scalar (.int value)))
              "p" (.scalar (.int (acc * value)))) (acc * value) rfl
          simpa [productBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            List.length_append, productValue, Int.mul_assoc] using next

private theorem product.result (xs : List Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (ints xs))) :
    HeapCalls.ReturnsValue program "product" [.ref address] heap (.scalar (.int (productValue xs))) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign HeapCalls.Evaluates.constant
  apply HeapCalls.BlockReturns.for_sequence (by intro expressions; simp)
    (HeapCalls.Evaluates.lookup rfl) (items := ints xs)
  · simp [Mutable.sequence, found]
  · let env := HeapCalls.setLocal
      (HeapCalls.argumentEnv [{ name := "xs", annotation := some (.subscript (.name "list") (.name "int")) }]
        [.ref address]) "p" (.scalar (.int 1))
    simpa using product.loop xs [] heap address (by simpa using found) env 1 rfl

private theorem square.result (n : Int) :
    HeapCalls.ReturnsValue program "square" [.scalar (.int n)] [] (.scalar (.int (n * n)))
      [.list (ints [n, n])] := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.call
    (.cons (HeapCalls.Evaluates.list (.cons (HeapCalls.Evaluates.lookup rfl)
      (.cons (HeapCalls.Evaluates.lookup rfl) .nil))) .nil)
  simpa [ints, productValue] using product.result [n, n] [.list (ints [n, n])] 0 rfl

private theorem reference.run (n : Int) :
    Finishes (scalarFunction program "reference" [.int n]).step
      (scalarFunction program "reference" [.int n]).initial (.ok (.int (n * n))) :=
  Execution.finishes_of_observe (fuel := 5) rfl

theorem square.«Equiv(reference)» (n : Int) :
    (HeapCalls.scalarFunction program "square" [.int n]).Equiv
      (scalarFunction program "reference" [.int n]) := by
  have run := HeapCalls.ReturnsValue.scalar_finishes (values := [.int n]) (square.result n)
  intro outcome
  constructor
  · intro h
    rw [h.unique run]
    exact reference.run n
  · intro h
    rw [h.unique (reference.run n)]
    exact run

theorem square.«Supported» :
    (∀ n : Int, (HeapCalls.scalarFunction program "square" [.int n]).Supported) ∧
    (∀ n : Int, (scalarFunction program "reference" [.int n]).Supported) :=
  ⟨fun n => (HeapCalls.ReturnsValue.scalar_returns (values := [.int n]) (square.result n)).supported,
   fun n => Execution.supported_of_finishes (reference.run n)⟩

theorem text_length.«Returns» (s : String) :
    (Calls.function program "text_length" [.string s]).Returns := by
  apply Calls.ReturnsValue.returns (value := .int s.length)
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  exact Calls.Evaluates.builtin (.cons (Calls.Evaluates.lookup rfl) .nil) rfl

end tests.py.sequences
