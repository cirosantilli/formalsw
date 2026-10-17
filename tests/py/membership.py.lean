import «.formalsw».tests.py.«membership.py.ast»
import FormalSW

namespace tests.py.membership
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := MembershipAst.module

private theorem tested (heap : Mutable.Heap) (n : Int) (xs : Nat) (items : List Int)
    (found : heap[xs]? = some (.list (items.map (fun n => .scalar (.int n)))))
    (env : Mutable.Env) (getN : env "n" = some (.scalar (.int n))) (getXs : env "xs" = some (.ref xs))
    (negated : Bool) :
    Evaluates program env (.membership (.name "n") (.name "xs") negated) heap
      (.scalar (.bool (if negated then !decide (n ∈ items) else decide (n ∈ items)))) heap := by
  exact Evaluates.membership (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getXs) .nil))
    (membership_list_ints heap xs n items found negated)

private theorem present.result (heap : Mutable.Heap) (n : Int) (xs : Nat) (items : List Int)
    (found : heap[xs]? = some (.list (items.map (fun n => .scalar (.int n))))) :
    ReturnsValue program "present" [.scalar (.int n), .ref xs] heap (.scalar (.bool (decide (n ∈ items)))) heap := by
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (tested heap n xs items found _ rfl rfl false)

private theorem absent.result (heap : Mutable.Heap) (n : Int) (xs : Nat) (items : List Int)
    (found : heap[xs]? = some (.list (items.map (fun n => .scalar (.int n))))) :
    ReturnsValue program "absent" [.scalar (.int n), .ref xs] heap (.scalar (.bool (!decide (n ∈ items)))) heap := by
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (tested heap n xs items found _ rfl rfl true)

private theorem restored.result (heap : Mutable.Heap) (n : Int) (xs : Nat) (items : List Int)
    (found : heap[xs]? = some (.list (items.map (fun n => .scalar (.int n))))) :
    ReturnsValue program "restored" [.scalar (.int n), .ref xs] heap (.scalar (.bool (decide (n ∈ items)))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.unary (tested heap n xs items found _ rfl rfl true)
  simp [HeapCalls.unary, Mutable.truth, scalarTruth]

theorem present.«Returns» (heap : Mutable.Heap) (n : Int) (xs : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref xs) "list[int]") :
    (HeapCalls.call program "present" [.scalar (.int n), .ref xs] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (present.result heap n xs items found).returns

theorem present.«Supported» (heap : Mutable.Heap) (n : Int) (xs : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref xs) "list[int]") :
    (HeapCalls.call program "present" [.scalar (.int n), .ref xs] heap).Supported :=
  (present.«Returns» heap n xs valid typed).supported

theorem absent.«Returns» (heap : Mutable.Heap) (n : Int) (xs : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref xs) "list[int]") :
    (HeapCalls.call program "absent" [.scalar (.int n), .ref xs] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (absent.result heap n xs items found).returns

theorem absent.«Supported» (heap : Mutable.Heap) (n : Int) (xs : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref xs) "list[int]") :
    (HeapCalls.call program "absent" [.scalar (.int n), .ref xs] heap).Supported :=
  (absent.«Returns» heap n xs valid typed).supported

theorem restored.«Equiv(present)» (heap : Mutable.Heap) (n : Int) (xs : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref xs) "list[int]") :
    (HeapCalls.call program "restored" [.scalar (.int n), .ref xs] heap).Equiv
      (HeapCalls.call program "present" [.scalar (.int n), .ref xs] heap) := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact Mutable.Call.equiv_of_finishes (restored.result heap n xs items found).finishes
    (present.result heap n xs items found).finishes (.inl rfl)

theorem restored.«Supported» :
    (∀ heap n xs, heap.Valid → Mutable.Value.HasType heap (.ref xs) "list[int]" →
      (HeapCalls.call program "restored" [.scalar (.int n), .ref xs] heap).Supported) ∧
    (∀ heap n xs, heap.Valid → Mutable.Value.HasType heap (.ref xs) "list[int]" →
      (HeapCalls.call program "present" [.scalar (.int n), .ref xs] heap).Supported) := by
  constructor
  · intro heap n xs _ typed
    obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
    exact (restored.result heap n xs items found).returns.supported
  · exact present.«Supported»

private theorem literal.result (n : Int) :
    ReturnsValue program "literal" [.scalar (.int n)] [] (.scalar (.bool (decide (n ∈ ([4, 6, 9, 11] : List Int)))))
      [.tuple ([4, 6, 9, 11].map (fun n => .scalar (.int n)))] := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.membership
    (.cons (Evaluates.lookup rfl)
      (.cons (Evaluates.tuple (.cons .constant (.cons .constant (.cons .constant (.cons .constant .nil)))) (by simp)) .nil))
  exact membership_tuple_ints _ 0 n [4, 6, 9, 11] rfl false

theorem literal.«Returns» (n : Int) : (HeapCalls.scalarFunction program "literal" [.int n]).Returns :=
  (literal.result n).scalar_returns

theorem literal.«Supported» (n : Int) : (HeapCalls.scalarFunction program "literal" [.int n]).Supported :=
  (literal.«Returns» n).supported

end tests.py.membership
