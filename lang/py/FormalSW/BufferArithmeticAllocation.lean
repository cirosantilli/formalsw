import lang.py.FormalSW.BufferAllocation
import lang.py.FormalSW.BufferArithmeticRelocation

/-! Allocating buffer arithmetic copies bytes after successful operand conversion. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

inductive BufferArithmeticInput (heap : Mutable.Heap) : BinOp → Value → Value → List UInt8 → Prop where
  | add (address : Nat) (bytes : List UInt8) (right : Value) (more : List UInt8)
      (found : heap[address]? = some (.bytearray bytes))
      (read : bufferOperand none right heap = some (.ok more, heap)) :
      BufferArithmeticInput heap .add (.ref address) right (bytes ++ more)
  | repeatBuffer (address : Nat) (bytes : List UInt8) (right : Value) (count : Int)
      (found : heap[address]? = some (.bytearray bytes))
      (read : Mutable.integer right heap = some (.ok count, heap)) :
      BufferArithmeticInput heap .mult (.ref address) right (List.replicate count.toNat bytes).flatten
  | countLeft (address : Nat) (count : Constant) (bytes : List UInt8)
      (input : BufferArithmeticInput heap .mult (.ref address) (.scalar count) bytes) :
      BufferArithmeticInput heap .mult (.scalar count) (.ref address) bytes

theorem BufferArithmeticInput.relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    {op : BinOp} {left right : Value} {bytes : List UInt8}
    (input : BufferArithmeticInput logical op left right bytes) (layout : ExecutionLayout logical physical rename)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length) :
    BufferArithmeticInput physical op (relocateValue rename left) (relocateValue rename right) bytes := by
  revert leftInside rightInside
  induction input with
  | add address bytes right more found read =>
    intro _ rightInside
    apply BufferArithmeticInput.add (rename address) bytes _ more (layout.runtime.lookup _ _ found)
    simpa only [read, Option.map, Option.map_none] using
      layout.runtime.bufferOperand none right (by intro address impossible; cases impossible) rightInside
  | repeatBuffer address bytes right count found read =>
    intro _ _
    apply BufferArithmeticInput.repeatBuffer (rename address) bytes _ count (layout.runtime.lookup _ _ found)
    simpa only [read, Option.map] using integer_relocates logical physical rename right
  | countLeft address count bytes input ih =>
    intro _ rightInside
    exact .countLeft (rename address) count bytes (ih rightInside (by trivial))

theorem BufferArithmeticInput.binary {heap : Mutable.Heap} {op : BinOp} {left right : Value} {bytes : List UInt8}
    (input : BufferArithmeticInput heap op left right bytes) :
    Mutable.binary op left right heap = some (.ok (.ref heap.length), heap ++ [.bytearray bytes]) := by
  induction input with
  | add address bytes right more found read =>
    rw [binary_add_buffer_eval heap address bytes right found]
    simp [read, Mutable.eval_bind, storeBufferResult, Mutable.allocateBuffer, Except.map]
  | repeatBuffer address bytes right count found read =>
    rw [binary_mult_buffer_eval heap address bytes right found]
    simp [read, Mutable.eval_bind, storeBufferResult, Mutable.allocateBuffer, Except.map]
  | countLeft address count bytes input ih => exact (binary_mult_ref_value_comm heap address (.scalar count)).trans ih

end FormalSW.PyAst.HeapCalls.Relocation
