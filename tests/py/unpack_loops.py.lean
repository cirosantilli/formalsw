import «.formalsw».tests.py.«unpack_loops.py.ast»
import FormalSW

namespace tests.py.unpack_loops
open FormalSW.PyAst
private abbrev program := UnpackLoopsAst.module
private abbrev body : List Stmt :=
  [.augAssign (.name "result") .add (.binOp (.binOp (.name "a") .mult (.name "n")) .add (.name "b"))]

private theorem loop.result (heap : Mutable.Heap) (table : Nat) (rows : List Nat)
    (found : heap[table]? = some (.list (rows.map Mutable.Value.ref)))
    (pairs : ∀ row ∈ rows, ∃ a b : Int, heap[row]? = some (.tuple [.scalar (.int a), .scalar (.int b)]))
    (position : Nat) (n acc : Int) (env : HeapCalls.Env)
    (getN : env "n" = some (.scalar (.int n))) (getAcc : env "result" = some (.scalar (.int acc))) :
    ∃ finalEnv answer, HeapCalls.BlockContinues program env
      [.unpackStepLoop ["a", "b"] (.ref table) position body []] heap finalEnv heap ∧
      finalEnv "result" = some (.scalar (.int answer)) := by
  have sequence : Mutable.sequence (.ref table) heap = some (.ok (rows.map Mutable.Value.ref), heap) := by
    simp [Mutable.sequence, found]
  by_cases active : position < rows.length
  · obtain ⟨a, b, pair⟩ := pairs rows[position] (List.getElem_mem active)
    let indexed := HeapCalls.assignNames env ["a", "b"] [.scalar (.int a), .scalar (.int b)]
    have savedN : indexed "n" = some (.scalar (.int n)) := by
      simpa [indexed, HeapCalls.assignNames, HeapCalls.setLocal] using getN
    have savedAcc : indexed "result" = some (.scalar (.int acc)) := by
      simpa [indexed, HeapCalls.assignNames, HeapCalls.setLocal] using getAcc
    have expression : HeapCalls.Evaluates program indexed
        (.binOp (.binOp (.name "a") .mult (.name "n")) .add (.name "b")) heap
        (.scalar (.int (a * n + b))) heap :=
      HeapCalls.Evaluates.binary
        (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup rfl) (HeapCalls.Evaluates.lookup savedN) rfl)
        (HeapCalls.Evaluates.lookup rfl) rfl
    let nextEnv := HeapCalls.setLocal indexed "result" (.scalar (.int (acc + (a * n + b))))
    have updated : HeapCalls.BlockContinues program indexed body heap nextEnv heap :=
      HeapCalls.BlockContinues.augAssign savedAcc expression rfl
    obtain ⟨finalEnv, answer, rest, result⟩ := loop.result heap table rows found pairs (position + 1)
      n (acc + (a * n + b)) nextEnv
      (by simpa [nextEnv, HeapCalls.setLocal] using savedN) rfl
    refine ⟨finalEnv, answer, ?_, result⟩
    apply HeapCalls.BlockContinues.unpack_step (source := .ref table) (value := .ref rows[position])
      (values := [.scalar (.int a), .scalar (.int b)]) sequence
      (by simp [List.getElem?_map, List.getElem?_eq_getElem active])
      (by simp [Mutable.sequence, pair]) rfl
    exact updated.append rest
  · exact ⟨env, acc, HeapCalls.BlockContinues.unpack_done (source := .ref table) sequence
      (by simp [List.getElem?_eq_none (by omega : rows.length ≤ position)]) HeapCalls.BlockContinues.nil, getAcc⟩
termination_by rows.length - position
decreasing_by omega

private abbrev tableHeap : Mutable.Heap :=
  [.tuple [.scalar (.int 0), .scalar (.int 1)], .tuple [.scalar (.int 1), .scalar (.int 0)],
   .tuple [.scalar (.int 1), .scalar (.int 1)], .tuple [.scalar (.int 1), .scalar (.int (-1))],
   .list [.ref 0, .ref 1, .ref 2, .ref 3]]

private theorem table.result (env : HeapCalls.Env) :
    HeapCalls.Evaluates program env
      (.list [.tuple [.constant (.int 0), .constant (.int 1)],
        .tuple [.constant (.int 1), .constant (.int 0)],
        .tuple [.constant (.int 1), .constant (.int 1)],
        .tuple [.constant (.int 1), .unaryOp .uSub (.constant (.int 1))]]) [] (.ref 4) tableHeap := by
  apply HeapCalls.Evaluates.list (finalHeap := tableHeap.take 4)
  refine .cons (HeapCalls.Evaluates.tuple (finalHeap := tableHeap.take 0) (.cons HeapCalls.Evaluates.constant (.cons HeapCalls.Evaluates.constant .nil)) (by decide)) ?_
  refine .cons (HeapCalls.Evaluates.tuple (finalHeap := tableHeap.take 1) (.cons HeapCalls.Evaluates.constant (.cons HeapCalls.Evaluates.constant .nil)) (by decide)) ?_
  refine .cons (HeapCalls.Evaluates.tuple (finalHeap := tableHeap.take 2) (.cons HeapCalls.Evaluates.constant (.cons HeapCalls.Evaluates.constant .nil)) (by decide)) ?_
  exact .cons (HeapCalls.Evaluates.tuple (finalHeap := tableHeap.take 3) (.cons HeapCalls.Evaluates.constant
    (.cons (HeapCalls.Evaluates.unary HeapCalls.Evaluates.constant rfl) .nil)) (by decide)) .nil

private theorem total.result (n : Int) :
    ∃ answer, HeapCalls.ReturnsValue program "total" [.scalar (.int n)] [] (.scalar (.int answer)) tableHeap := by
  let env := HeapCalls.setLocal (HeapCalls.setLocal
    (HeapCalls.argumentEnv [⟨"n", some (.name "int"), none⟩] [.scalar (.int n)]) "directions" (.ref 4))
    "result" (.scalar (.int 0))
  have pairs : ∀ row ∈ [0, 1, 2, 3], ∃ a b : Int,
      tableHeap[row]? = some (.tuple [.scalar (.int a), .scalar (.int b)]) := by
    intro row member
    have alternatives : row = 0 ∨ row = 1 ∨ row = 2 ∨ row = 3 := by simpa using member
    rcases alternatives with rfl | rfl | rfl | rfl
    · exact ⟨0, 1, rfl⟩
    · exact ⟨1, 0, rfl⟩
    · exact ⟨1, 1, rfl⟩
    · exact ⟨1, -1, rfl⟩
  obtain ⟨finalEnv, answer, loop, result⟩ := loop.result tableHeap 4 [0, 1, 2, 3] rfl pairs 0 n 0 env rfl rfl
  refine ⟨answer, HeapCalls.BlockReturns.function rfl rfl ?_⟩
  apply HeapCalls.BlockContinues.returns (HeapCalls.BlockContinues.annAssign (table.result _))
  apply HeapCalls.BlockContinues.returns (HeapCalls.BlockContinues.annAssign HeapCalls.Evaluates.constant)
  apply HeapCalls.BlockContinues.returns (HeapCalls.BlockContinues.for_unpack
    (by intro expressions impossible; cases impossible) rfl (HeapCalls.Evaluates.lookup (name := "directions") rfl)
    (by rfl) loop)
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup result)

theorem total.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "total" [.int n]).Returns := by
  obtain ⟨answer, executed⟩ := total.result n
  exact executed.scalar_returns

theorem total.«ReturnType» (n : Int) :
    (HeapCalls.scalarFunction program "total" [.int n]).ReturnType "int" := by
  obtain ⟨answer, executed⟩ := total.result n
  exact .inr ⟨_, executed.scalar_finishes, rfl⟩

theorem total.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "total" [.int n]).Supported := by
  obtain ⟨answer, executed⟩ := total.result n
  exact Execution.supported_of_finishes executed.scalar_finishes

private theorem annotated.result (n : Int) :
    Calls.ReturnsValue program "annotated" [.int n] (.int (n + 1)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.annAssign
    (Calls.Evaluates.binary (Calls.Evaluates.lookup rfl) Calls.Evaluates.constant rfl)
  apply Calls.BlockReturns.annotation
  exact Calls.BlockReturns.return_value (Calls.Evaluates.lookup rfl)

theorem annotated.«Returns» (n : Int) :
    (Calls.function program "annotated" [.int n]).Returns := (annotated.result n).returns

theorem annotated.«ReturnType» (n : Int) :
    (Calls.function program "annotated" [.int n]).ReturnType "int" :=
  .inr ⟨_, (annotated.result n).finishes, rfl⟩

end tests.py.unpack_loops
