import lang.py.FormalSW.HeapCalls
import lang.py.FormalSW.PrimitiveWork

/-! Tariffs for contiguous byte buffers. Copying and allocation pay per byte;
extended slice replacement pays per written byte. Resizing or deleting a slice
also pays for moving the suffix. Bounds and address arithmetic respect the
selected integer policy. Custom index/conversion protocols remain unpriced. -/
namespace FormalSW.PyAst.HeapCalls.BufferWork
open PrimitiveWork

def bound (arithmetic : Arithmetic) : Value → Option Nat
  | .scalar .none => some 1
  | .scalar value => (scalarNumber value).map (integer arithmetic)
  | _ => none

def sliceWidth (arithmetic : Arithmetic) (length : Nat)
    (lower upper stride : Value) : Option Nat := do
  return 1 + integer arithmetic length + (← bound arithmetic lower) +
    (← bound arithmetic upper) + (← bound arithmetic stride)

/-- Normalizing a slice includes division. Contiguous replacement and empty
replacement can move the whole old buffer, including extended-slice deletion. -/
def slice (arithmetic : Arithmetic) (length : Nat) (lower upper stride : Value)
    (replacement : List UInt8) : Option Nat := do
  let width ← sliceWidth arithmetic length lower upper stride
  let contiguous := match stride with
    | .scalar .none => true
    | .scalar value => scalarNumber value == some 1
    | _ => false
  let moved := replacement.length + if contiguous || replacement.isEmpty then length else 0
  return 8 * width * width + (moved + 1) * width

def repetition (arithmetic : Arithmetic) (heap : Heap) (op : BinOp) (left right : Value) : Option Nat :=
  match op, left, right with
  | .mult, .ref address, .scalar count | .mult, .scalar count, .ref address => do
      let count ← scalarNumber count
      match heap[address]? with
      | some (.bytearray bytes) => some (bytes.length * count.toNat + integer arithmetic count + 1)
      | _ => none
  | _, _, _ => none

def operation (arithmetic : Arithmetic) (heap : Heap) (op : Operation) (values : List Value) : Option Nat :=
  match op, values with
  | .builtin .bytearray, [] => some 1
  | .builtin .bytearray, [.scalar (.bytes bytes)] => some (bytes.length + 1)
  | .builtin .bytearray, [.scalar count] => do
      let count ← scalarNumber count
      return count.toNat + integer arithmetic count + 1
  | .builtin .bytearray, [.ref address] => match heap[address]? with
      | some (.bytearray bytes) => some (bytes.length + 1)
      | _ => none
  | .subscript, [.ref address, .scalar index] => do
      let index ← scalarNumber index
      match heap[address]? with
      | some (.bytearray bytes) => some (integer arithmetic index + integer arithmetic bytes.length + 1)
      | _ => none
  | .setItem (.scalar value), [.ref address, .scalar index] => do
      let index ← scalarNumber index
      let value ← scalarNumber value
      match heap[address]? with
      | some (.bytearray bytes) =>
          some (integer arithmetic index + integer arithmetic bytes.length + integer arithmetic value + 1)
      | _ => none
  | .setSlice (.scalar (.bytes replacement)), [.ref address, lower, upper, stride] =>
      match heap[address]? with
      | some (.bytearray bytes) => slice arithmetic bytes.length lower upper stride replacement
      | _ => none
  | _, _ => none

end FormalSW.PyAst.HeapCalls.BufferWork
