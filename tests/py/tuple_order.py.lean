import «.formalsw».tests.py.«tuple_order.py.ast»
import lang.py.FormalSW.TupleComparisons
import lang.py.FormalSW.ContainerTypes

namespace tests.py.tuple_order
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := TupleOrderAst.module
private abbrev integers : Mutable.ContainerType := .tupleOf (.scalar "int")
private abbrev numbers (xs : List Int) : List Mutable.Value := xs.map fun n => .scalar (.int n)
private abbrev flag (answer : Bool) : Mutable.Value := .scalar (.bool answer)

private theorem contents (heap : Heap) (address : Nat)
    (typed : Mutable.Value.HasContainerType heap (.ref address) integers) :
    ∃ xs : List Int, heap[address]? = some (.tuple (numbers xs)) := by
  obtain ⟨items, found, elements⟩ := Mutable.Value.hasContainerType_variadicTuple_iff.mp typed
  have projected : ∃ xs : List Int, items = numbers xs := by
    clear found
    induction items with
    | nil => exact ⟨[], rfl⟩
    | cons first rest ih =>
        obtain ⟨n, rfl⟩ := Mutable.Value.hasContainerType_int_iff.mp (elements first (by simp))
        obtain ⟨xs, rfl⟩ := ih (fun item member => elements item (List.mem_cons_of_mem _ member))
        exact ⟨n :: xs, rfl⟩
  obtain ⟨xs, rfl⟩ := projected
  exact ⟨xs, found⟩

theorem less.result (heap : Heap) (a b : Nat) (xs ys : List Int)
    (left : heap[a]? = some (.tuple (numbers xs))) (right : heap[b]? = some (.tuple (numbers ys))) :
    ReturnsValue program "less" [.ref a, .ref b] heap (flag (HeapSort.lexInt xs ys)) heap := by
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.compare (Evaluates.lookup rfl) (Evaluates.lookup rfl)
    (compare_int_tuple_lt heap a b xs ys left right))

theorem greater.result (heap : Heap) (a b : Nat) (xs ys : List Int)
    (left : heap[a]? = some (.tuple (numbers xs))) (right : heap[b]? = some (.tuple (numbers ys))) :
    ReturnsValue program "greater" [.ref a, .ref b] heap (flag (HeapSort.lexInt ys xs)) heap := by
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.compare (Evaluates.lookup rfl) (Evaluates.lookup rfl)
    (compare_int_tuple_gt heap a b xs ys left right))

private theorem less.typed_result (heap : Heap) (a b : Nat)
    (left : Mutable.Value.HasContainerType heap (.ref a) integers)
    (right : Mutable.Value.HasContainerType heap (.ref b) integers) :
    ∃ answer, ReturnsValue program "less" [.ref a, .ref b] heap (flag answer) heap := by
  obtain ⟨xs, foundLeft⟩ := contents heap a left
  obtain ⟨ys, foundRight⟩ := contents heap b right
  exact ⟨_, less.result heap a b xs ys foundLeft foundRight⟩

private theorem greater.typed_result (heap : Heap) (a b : Nat)
    (left : Mutable.Value.HasContainerType heap (.ref a) integers)
    (right : Mutable.Value.HasContainerType heap (.ref b) integers) :
    ∃ answer, ReturnsValue program "greater" [.ref a, .ref b] heap (flag answer) heap := by
  obtain ⟨xs, foundLeft⟩ := contents heap a left
  obtain ⟨ys, foundRight⟩ := contents heap b right
  exact ⟨_, greater.result heap a b xs ys foundLeft foundRight⟩

theorem less.«Returns» (heap : Heap) (a b : Nat) (_valid : heap.Valid)
    (left : Mutable.Value.HasContainerType heap (.ref a) integers)
    (right : Mutable.Value.HasContainerType heap (.ref b) integers) :
    (HeapCalls.call program "less" [.ref a, .ref b] heap).Returns := by
  obtain ⟨answer, result⟩ := less.typed_result heap a b left right
  exact result.returns

theorem less.«ReturnType» (heap : Heap) (a b : Nat) (_valid : heap.Valid)
    (left : Mutable.Value.HasContainerType heap (.ref a) integers)
    (right : Mutable.Value.HasContainerType heap (.ref b) integers) :
    (HeapCalls.call program "less" [.ref a, .ref b] heap).ReturnType "bool" := by
  obtain ⟨answer, result⟩ := less.typed_result heap a b left right
  exact .inr ⟨flag answer, [], heap, heap.length, result.finishes, rfl⟩

theorem less.«Supported» (heap : Heap) (a b : Nat) (valid : heap.Valid)
    (left : Mutable.Value.HasContainerType heap (.ref a) integers)
    (right : Mutable.Value.HasContainerType heap (.ref b) integers) :
    (HeapCalls.call program "less" [.ref a, .ref b] heap).Supported := (less.«Returns» heap a b valid left right).supported

theorem greater.«Returns» (heap : Heap) (a b : Nat) (_valid : heap.Valid)
    (left : Mutable.Value.HasContainerType heap (.ref a) integers)
    (right : Mutable.Value.HasContainerType heap (.ref b) integers) :
    (HeapCalls.call program "greater" [.ref a, .ref b] heap).Returns := by
  obtain ⟨answer, result⟩ := greater.typed_result heap a b left right
  exact result.returns

theorem greater.«ReturnType» (heap : Heap) (a b : Nat) (_valid : heap.Valid)
    (left : Mutable.Value.HasContainerType heap (.ref a) integers)
    (right : Mutable.Value.HasContainerType heap (.ref b) integers) :
    (HeapCalls.call program "greater" [.ref a, .ref b] heap).ReturnType "bool" := by
  obtain ⟨answer, result⟩ := greater.typed_result heap a b left right
  exact .inr ⟨flag answer, [], heap, heap.length, result.finishes, rfl⟩

theorem greater.«Supported» (heap : Heap) (a b : Nat) (valid : heap.Valid)
    (left : Mutable.Value.HasContainerType heap (.ref a) integers)
    (right : Mutable.Value.HasContainerType heap (.ref b) integers) :
    (HeapCalls.call program "greater" [.ref a, .ref b] heap).Supported := (greater.«Returns» heap a b valid left right).supported

end tests.py.tuple_order
