import «.formalsw».tests.py.«record_inputs.py.ast»
import FormalSW

namespace tests.py.record_inputs
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := RecordInputsAst.module
private abbrev origin := (program.classOrigins.lookup "Record").getD ""
private abbrev Typed (heap : Mutable.Heap) (address : Nat) :=
  Mutable.Value.HasRecordType heap (.ref address) origin "Record" true [("value", "int"), ("items", "list[int]")]

private theorem integer_field (heap : Mutable.Heap) (value : Mutable.Value)
    (typed : Mutable.Value.HasType heap value "int") : ∃ n : Int, value = .scalar (.int n) := by
  cases value with
  | scalar value => cases value <;> simp_all [Mutable.Value.HasType]
  | ref address =>
      change ∃ items, heap[address]? = some (.list items) ∧
        ("int" = "list" ∨ ∃ kind, ∃ (_ : "int" = "list[" ++ kind ++ "]"), _) at typed
      obtain ⟨items, found, domain⟩ := typed
      rcases domain with impossible | ⟨kind, same, _⟩
      · simp at impossible
      · have size := congrArg String.length same
        rw [String.length_append, String.length_append] at size
        change 3 = 5 + kind.length + 1 at size
        omega

private theorem field_result (heap : Mutable.Heap) (address : Nat) (typed : Typed heap address) :
    ∃ n : Int, ∀ (env : Mutable.Env) (name : String), env name = some (.ref address) →
      Evaluates program env (.attribute (.name name) "value") heap (.scalar (.int n)) heap := by
  obtain ⟨fields, found, types⟩ := typed
  obtain ⟨value, lookup, typedValue⟩ := types ("value", "int") (by simp)
  obtain ⟨n, rfl⟩ := integer_field heap value typedValue
  refine ⟨n, ?_⟩
  intro env name getRecord
  apply Evaluates.field (Evaluates.lookup getRecord)
  simp [getAttribute, instanceClass, found, lookup, program, RecordInputsAst.module,
    Module.findClass, Module.findClassBody, findClassBodyIn, origin]

private theorem read_result (heap : Mutable.Heap) (address : Nat) (typed : Typed heap address) :
    ∃ value, ReturnsValue program "read" [.ref address] heap value heap := by
  obtain ⟨n, field⟩ := field_result heap address typed
  refine ⟨.scalar (.int n), ?_⟩
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (field _ "record" rfl)

private theorem copied_result (heap : Mutable.Heap) (address : Nat) (typed : Typed heap address) :
    ∃ value, ReturnsValue program "copied" [.ref address] heap value heap ∧
      ReturnsValue program "read" [.ref address] heap value heap := by
  obtain ⟨n, field⟩ := field_result heap address typed
  refine ⟨.scalar (.int n), ?_, ?_⟩
  · apply BlockReturns.function rfl rfl
    apply BlockReturns.assign (field _ "record" rfl)
    exact BlockReturns.return_value (Evaluates.lookup rfl)
  · apply BlockReturns.function rfl rfl
    exact BlockReturns.return_value (field _ "record" rfl)

theorem read.«Returns» (heap : Mutable.Heap) (record : Nat) (_valid : heap.Valid) (typed : Typed heap record) :
    (HeapCalls.call program "read" [.ref record] heap).Returns := by
  obtain ⟨value, result⟩ := read_result heap record typed
  exact result.returns

theorem read.«Supported» (heap : Mutable.Heap) (record : Nat) (valid : heap.Valid) (typed : Typed heap record) :
    (HeapCalls.call program "read" [.ref record] heap).Supported := (read.«Returns» heap record valid typed).supported

theorem copied.«Equiv(read)» (heap : Mutable.Heap) (record : Nat) (_valid : heap.Valid) (typed : Typed heap record) :
    (HeapCalls.call program "copied" [.ref record] heap).Equiv (HeapCalls.call program "read" [.ref record] heap) := by
  obtain ⟨value, left, right⟩ := copied_result heap record typed
  exact Mutable.Call.equiv_of_finishes left.finishes right.finishes (.inl rfl)

theorem copied.«Supported» :
    (∀ heap record, heap.Valid → Typed heap record → (HeapCalls.call program "copied" [.ref record] heap).Supported) ∧
    (∀ heap record, heap.Valid → Typed heap record → (HeapCalls.call program "read" [.ref record] heap).Supported) := by
  constructor
  · intro heap record _ typed
    obtain ⟨value, result, _⟩ := copied_result heap record typed
    exact result.returns.supported
  · exact read.«Supported»

theorem total.«Returns» (heap : Mutable.Heap) (left right : Nat) (_valid : heap.Valid)
    (leftTyped : Typed heap left) (rightTyped : Typed heap right) :
    (HeapCalls.call program "total" [.ref left, .ref right] heap).Returns := by
  obtain ⟨a, leftField⟩ := field_result heap left leftTyped
  obtain ⟨b, rightField⟩ := field_result heap right rightTyped
  have result : ReturnsValue program "total" [.ref left, .ref right] heap (.scalar (.int (a + b))) heap := by
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    exact Evaluates.binary (leftField _ "left" rfl) (rightField _ "right" rfl) rfl
  exact result.returns

theorem total.«Supported» (heap : Mutable.Heap) (left right : Nat) (valid : heap.Valid)
    (leftTyped : Typed heap left) (rightTyped : Typed heap right) :
    (HeapCalls.call program "total" [.ref left, .ref right] heap).Supported :=
  (total.«Returns» heap left right valid leftTyped rightTyped).supported

private abbrev Guard (heap : Mutable.Heap) (record : Nat) :=
  HeapCalls.Condition program (fun key => if key = "record" then some (.ref record) else none)
    RecordInputsAst.requires_guarded_0 heap

private theorem guarded_result (heap : Mutable.Heap) (record : Nat) (typed : Typed heap record) :
    ∃ value, ReturnsValue program "guarded" [.ref record] heap value heap ∧
      ReturnsValue program "read" [.ref record] heap value heap := by
  obtain ⟨n, field⟩ := field_result heap record typed
  refine ⟨.scalar (.int n), ?_, ?_⟩
  all_goals
    apply BlockReturns.function rfl rfl
    exact BlockReturns.return_value (field _ "record" rfl)

theorem guarded.«Equiv(read)» (heap : Mutable.Heap) (record : Nat) (_valid : heap.Valid)
    (typed : Typed heap record) (_guard : Guard heap record) :
    (HeapCalls.call program "guarded" [.ref record] heap).Equiv (HeapCalls.call program "read" [.ref record] heap) := by
  obtain ⟨value, left, right⟩ := guarded_result heap record typed
  exact Mutable.Call.equiv_of_finishes left.finishes right.finishes (.inl rfl)

theorem guarded.«Supported» :
    (∀ heap record, heap.Valid → Typed heap record → Guard heap record →
      (HeapCalls.call program "guarded" [.ref record] heap).Supported) ∧
    (∀ heap record, heap.Valid → Typed heap record → Guard heap record →
      (HeapCalls.call program "read" [.ref record] heap).Supported) := by
  constructor
  · intro heap record _ typed _
    obtain ⟨value, result, _⟩ := guarded_result heap record typed
    exact result.returns.supported
  · intro heap record valid typed _
    exact read.«Supported» heap record valid typed

theorem requires_guarded_0_supported (heap : Mutable.Heap) (record : Nat) (_valid : heap.Valid)
    (typed : Typed heap record) :
    (HeapCalls.evaluate program (fun key => if key = "record" then some (.ref record) else none)
      RecordInputsAst.requires_guarded_0 heap).Supported := by
  obtain ⟨n, field⟩ := field_result heap record typed
  have evaluation : Evaluates program (fun key => if key = "record" then some (.ref record) else none)
      RecordInputsAst.requires_guarded_0 heap (.scalar (.bool (decide (n ≥ 0)))) heap := by
    exact Evaluates.compare (field _ "record" rfl) Evaluates.constant rfl
  exact Execution.supported_of_finishes evaluation.finishes

end tests.py.record_inputs
