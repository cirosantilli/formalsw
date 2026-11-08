import lang.py.FormalSW.HeapBufferWork

/-! Costs for fresh list slices and concatenation. Slice normalization respects
signed bounds and stride; copying pays for the selected element references.
Integer widths affect bounds and iterator arithmetic, not the referenced data. -/
namespace FormalSW.PyAst.HeapCalls.SequenceWork
open PrimitiveWork

def optionalIndex : Value → Option (Option Int)
  | .scalar .none => some none
  | .scalar value => (scalarNumber value).map some
  | _ => none

def slice (arithmetic : Arithmetic) (length : Nat) (lower upper stride : Value) : Option Nat := do
  let width ← BufferWork.sliceWidth arithmetic length lower upper stride
  let bounds : Py.Builtin.Slice.Slice :=
    ⟨← optionalIndex lower, ← optionalIndex upper, ← optionalIndex stride⟩
  let indices ← (Py.Builtin.Slice.indexList bounds length).toOption
  return 8 * width * width + indices.length * (width + 1) + 1

def concatenate (arithmetic : Arithmetic) (heap : Heap) (left right : Value) : Option Nat :=
  match left, right with
  | .ref left, .ref right => match heap[left]?, heap[right]? with
      | some (.list ls), some (.list rs) =>
          some (ls.length + rs.length + integer arithmetic ls.length + integer arithmetic rs.length + 1)
      | _, _ => none
  | _, _ => none

theorem slice_prefix (length : Nat) (stop : Int) :
    slice .word length (.scalar .none) (.scalar (.int stop)) (.scalar .none) =
      some (6 * Py.Builtin.Slice.prefixLength length stop + 201) := by
  simp [slice, optionalIndex, BufferWork.sliceWidth, BufferWork.bound, scalarNumber,
    integer, Py.Builtin.Slice.indexList_prefix, Except.toOption]
  omega

theorem slice_suffix (length start : Nat) :
    slice .word length (.scalar (.int start)) (.scalar .none) (.scalar .none) =
      some (6 * (length-start) + 201) := by
  simp [slice, optionalIndex, BufferWork.sliceWidth, BufferWork.bound, scalarNumber,
    integer, Py.Builtin.Slice.indexList_suffix, Except.toOption]
  omega

end FormalSW.PyAst.HeapCalls.SequenceWork
