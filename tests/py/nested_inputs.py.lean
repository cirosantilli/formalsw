import «.formalsw».tests.py.«nested_inputs.py.ast»
import FormalSW

namespace tests.py.nested_inputs
open FormalSW.PyAst
private abbrev program := NestedInputsAst.module
private abbrev body : List Stmt :=
  [.augAssign (.name "total") .add (.builtinCall .len [.name "row"])]

private theorem loop.result (heap : Mutable.Heap) (address : Nat) (rows : List Nat)
    (found : heap[address]? = some (.list (rows.map Mutable.Value.ref)))
    (typed : ∀ row ∈ rows, Mutable.Value.HasType heap (.ref row) "list[int]")
    (position : Nat) (bounded : position ≤ rows.length)
    (env : HeapCalls.Env) (total : Int) (getTotal : env "total" = some (.scalar (.int total))) :
    ∃ finalEnv answer, HeapCalls.BlockContinues program env
      [.sequenceStepLoop "row" (.ref address) position body []] heap finalEnv heap ∧
      finalEnv "total" = some (.scalar (.int answer)) := by
  have sequence : Mutable.sequence (.ref address) heap = some (.ok (rows.map Mutable.Value.ref), heap) := by
    simp [Mutable.sequence, found]
  by_cases active : position < rows.length
  · let row := rows[position]
    obtain ⟨values, contents⟩ := Mutable.Value.ints_of_hasType (typed row (List.getElem_mem active))
    let boundEnv := HeapCalls.setLocal env "row" (.ref row)
    let nextEnv := HeapCalls.setLocal boundEnv "total" (.scalar (.int (total + values.length)))
    have saved : boundEnv "total" = some (.scalar (.int total)) := by
      simpa [boundEnv, HeapCalls.setLocal] using getTotal
    have step : HeapCalls.BlockContinues program boundEnv body heap nextEnv heap := by
      apply HeapCalls.BlockContinues.augAssign saved (right := .scalar (.int values.length)) (middle := heap)
      · apply HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup rfl) .nil)
        simp [HeapCalls.primitive, Mutable.length, contents]
      · rfl
    obtain ⟨finalEnv, answer, rest, finalTotal⟩ := loop.result heap address rows found typed
      (position + 1) (by omega) nextEnv (total + values.length) rfl
    refine ⟨finalEnv, answer, ?_, finalTotal⟩
    apply HeapCalls.BlockContinues.sequence_step (source := .ref address) (value := .ref row) sequence
      (by simp [List.getElem?_map, List.getElem?_eq_getElem active, row])
    exact step.append rest
  · refine ⟨env, total, ?_, getTotal⟩
    apply HeapCalls.BlockContinues.sequence_done (source := .ref address) sequence
      (by simp [List.getElem?_eq_none (by omega : rows.length ≤ position)]) HeapCalls.BlockContinues.nil
termination_by rows.length - position
decreasing_by omega

private theorem count_cells.result (heap : Mutable.Heap) (address : Nat)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    ∃ answer, HeapCalls.ReturnsValue program "count_cells" [.ref address] heap (.scalar (.int answer)) heap := by
  obtain ⟨rows, found, types⟩ := Mutable.Value.lists_of_hasType typed
  let initialEnv := HeapCalls.setLocal (HeapCalls.argumentEnv
    [⟨"rows", some (.subscript (.name "list") (.subscript (.name "list") (.name "int"))), none⟩]
    [.ref address]) "total" (.scalar (.int 0))
  obtain ⟨finalEnv, answer, loop, result⟩ := loop.result heap address rows found types 0 (by omega) initialEnv 0 rfl
  refine ⟨answer, ?_⟩
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign HeapCalls.Evaluates.constant
  apply HeapCalls.BlockContinues.returns
    (HeapCalls.BlockContinues.for_sequence (items := rows.map Mutable.Value.ref)
      (by intros expressions impossible; cases impossible)
      (HeapCalls.Evaluates.lookup (name := "rows") rfl)
      (by simp [Mutable.sequence, found]) loop)
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup result)

theorem count_cells.«Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "count_cells" [.ref address] heap).Returns := by
  obtain ⟨answer, executed⟩ := count_cells.result heap address typed
  exact executed.returns

theorem count_cells.«ReturnType» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "count_cells" [.ref address] heap).ReturnType "int" := by
  obtain ⟨answer, executed⟩ := count_cells.result heap address typed
  exact .inr ⟨_, [], heap, heap.length, executed.finishes, rfl⟩

theorem count_cells.«Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "count_cells" [.ref address] heap).Supported :=
  (count_cells.«Returns» heap address valid typed).supported

private theorem identity.result (heap : Mutable.Heap) (address : Nat) :
    HeapCalls.ReturnsValue program "identity" [.ref address] heap (.ref address) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

theorem identity.«Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (_typed : Mutable.Value.HasType heap (.ref address) "list[list[list[str]]]") :
    (HeapCalls.call program "identity" [.ref address] heap).Returns :=
  (identity.result heap address).returns

theorem identity.«ReturnType» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[list[str]]]") :
    (HeapCalls.call program "identity" [.ref address] heap).ReturnType "list[list[list[str]]]" :=
  .inr ⟨_, [], heap, heap.length, (identity.result heap address).finishes, typed⟩

theorem identity.«Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[list[str]]]") :
    (HeapCalls.call program "identity" [.ref address] heap).Supported :=
  (identity.«Returns» heap address valid typed).supported

end tests.py.nested_inputs
