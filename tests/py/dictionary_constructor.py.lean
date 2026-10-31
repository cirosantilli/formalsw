import «.formalsw».tests.py.«dictionary_constructor.py.ast»
import FormalSW

namespace tests.py.dictionary_constructor
open FormalSW.PyAst
private abbrev program := DictionaryConstructorAst.module

theorem copy.result (heap : Mutable.Heap) (address : Nat)
    (entries : List (Constant × Mutable.Value))
    (found : heap[address]? = some (.dict entries)) :
    HeapCalls.ReturnsValue program "copy" [.ref address] heap (.ref heap.length)
      (heap ++ [.dict entries]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup rfl) .nil)
    (HeapCalls.primitive_dict_copy heap address entries found)

theorem copy.«Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "dict[str,int]") :
    (HeapCalls.call program "copy" [.ref address] heap).Returns := by
  obtain ⟨entries, found, _⟩ := Mutable.Value.dictionary_of_hasType typed rfl
  exact (copy.result heap address entries found).returns

theorem copy.«ReturnType» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "dict[str,int]") :
    (HeapCalls.call program "copy" [.ref address] heap).ReturnType "dict[str,int]" := by
  obtain ⟨entries, found, types⟩ := Mutable.Value.dictionary_of_hasType typed rfl
  refine .inr ⟨.ref heap.length, [], _, heap.length,
    (copy.result heap address entries found).finishes, ?_⟩
  change Mutable.Value.DictionaryHasType (heap ++ [.dict entries]) (.ref heap.length) "str" "int"
  exact ⟨entries, by simp, types⟩

theorem copy.«Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "dict[str,int]") :
    (HeapCalls.call program "copy" [.ref address] heap).Supported :=
  (copy.«Returns» heap address valid typed).supported

/-- Updating a fresh dictionary never changes the source dictionary's binding. -/
theorem solve.result (n : Int) :
    HeapCalls.ReturnsValue program "solve" [.scalar (.int n)] [] (.scalar (.int n))
      [.dict [(.string "n", .scalar (.int n))],
        .dict [(.string "n", .scalar (.int (n + 1)))]] := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign
  · apply HeapCalls.Evaluates.dictionary
    exact .cons HeapCalls.Evaluates.constant (HeapCalls.Evaluates.lookup rfl) .nil
  apply HeapCalls.BlockReturns.assign
  · apply HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup rfl) .nil)
    exact HeapCalls.primitive_dict_copy _ 0 _ rfl
  apply HeapCalls.BlockReturns.setItem (by intros; simp)
  · exact HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup rfl)
      HeapCalls.Evaluates.constant rfl
  · exact .cons (HeapCalls.Evaluates.lookup rfl) (.cons HeapCalls.Evaluates.constant .nil)
  · exact Mutable.setItem_dictionary _ 1 _ rfl (.string "n") (.scalar (.int (n + 1)))
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.subscript (by intros; simp)
    (HeapCalls.Evaluates.lookup rfl) HeapCalls.Evaluates.constant
  exact Mutable.getItem_dictionary _ 0 _ rfl (.string "n") rfl

private theorem reference.result (n : Int) :
    Finishes (scalarFunction program "reference" [.int n]).step
      (scalarFunction program "reference" [.int n]).initial (.ok (.int n)) :=
  .done rfl

theorem solve.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "solve" [.int n]).Returns :=
  (solve.result n).scalar_returns

theorem solve.«Equiv(reference)» (n : Int) :
    (HeapCalls.scalarFunction program "solve" [.int n]).Equiv
      (scalarFunction program "reference" [.int n]) := by
  intro outcome
  constructor
  · intro run
    rw [run.unique (solve.result n).scalar_finishes]
    exact reference.result n
  · intro run
    rw [run.unique (reference.result n)]
    exact (solve.result n).scalar_finishes

theorem solve.«Supported» :
    (∀ n : Int, (HeapCalls.scalarFunction program "solve" [.int n]).Supported) ∧
      (∀ n : Int, (scalarFunction program "reference" [.int n]).Supported) :=
  ⟨fun n => (solve.«Returns» n).supported,
    fun n => Execution.supported_of_finishes (reference.result n)⟩

end tests.py.dictionary_constructor
