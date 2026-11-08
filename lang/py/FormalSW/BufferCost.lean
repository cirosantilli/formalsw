import lang.py.FormalSW.WeightedExecutionCost
import lang.py.FormalSW.HeapCalls

/-! Byte work needed by Python sieve proofs. Charges one per transition, fresh
bytearray storage, bytes produced by binary operations, and successful buffer
item/slice writes (including writes that leave the value unchanged). This is an
explicit model, not a claim about CPython's allocator or bit-operation costs. -/
namespace FormalSW.PyAst.HeapCalls.BufferCost

def bufferSlots (heap : Heap) : Nat :=
  (heap.map fun object => match object with | .bytearray bytes => bytes.length | _ => 0).sum

def byteLength (heap : Heap) : Value → Nat
  | .scalar (.bytes bytes) => bytes.length
  | .ref address => match heap[address]? with
      | some (.bytearray bytes) => bytes.length
      | some (.list items) | some (.tuple items) => items.length
      | _ => 0
  | _ => 0

def isBuffer (heap : Heap) (address : Nat) : Bool :=
  match heap[address]? with | some (.bytearray _) => true | _ => false

/-- Binary bytes construction is charged once, when the result is produced. -/
def scalarBytes (initial following : State) : Nat :=
  match initial.work, initial.stack, following.work with
  | .value _, .binaryRight _ _ _ :: _, .value (.scalar (.bytes bytes)) => bytes.length
  | _, _, _ => 0

/-- Writes are charged by their length, not by how many byte values change.
Only the successful primitive transition can incur this charge. -/
def writtenBytes (initial following : State) : Nat :=
  match initial.work, following.work with
  | .operation (.setSlice replacement) [.ref address, _, _, _], .value (.scalar .none) =>
      if isBuffer initial.heap address then byteLength initial.heap replacement else 0
  | .operation (.setItem _) [.ref address, _], .value (.scalar .none) =>
      if isBuffer initial.heap address then 1 else 0
  | _, _ => 0

def finalSlots : Except ExceptionObject Completion → Nat
  | .ok completion => bufferSlots completion.heap
  | .error _ => 0

def charge (module : Module) (anchors : Nat) (initial : State) : Nat :=
  1 + match step module anchors initial with
    | .next following => (bufferSlots following.heap - bufferSlots initial.heap) +
        scalarBytes initial following + writtenBytes initial following
    | .done outcome => finalSlots outcome - bufferSlots initial.heap
    | .unsupported => 0

theorem positive (module : Module) (anchors : Nat) (initial : State) :
    1 ≤ charge module anchors initial := by unfold charge; omega

/-- Weighted traces cover all net growth in bytearray storage. -/
theorem allocated_le (run : FinishesWith (step module anchors) (charge module anchors) state cost outcome) :
    finalSlots outcome ≤ bufferSlots state.heap + cost := by
  have bound (a b c d : Nat) : a ≤ b + (1 + (a - b + c + d)) := by omega
  apply run.potential (fun state => bufferSlots state.heap) finalSlots
  · intro s result finished
    simpa only [charge, finished, Nat.add_zero] using bound (finalSlots result) (bufferSlots s.heap) 0 0
  · intro s next transition
    simp only [charge, transition]
    exact bound _ _ _ _

theorem writes_le (transition : step module anchors initial = .next following) :
    writtenBytes initial following ≤ charge module anchors initial := by
  have bound (a b c : Nat) : c ≤ 1 + (a + b + c) := by omega
  simp only [charge, transition]
  exact bound _ _ _

end FormalSW.PyAst.HeapCalls.BufferCost
