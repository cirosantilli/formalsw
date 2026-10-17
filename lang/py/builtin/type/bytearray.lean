import lang.py.builtin.type.bytes

/-! Python `bytearray`: mutable byte sequences represented by pure state transitions. -/

namespace FormalSW.Py.Builtin.ByteArray

open FormalSW.Py.Builtin

abbrev ByteArray := Bytes.ByteString

def empty : ByteArray := []
def ofBytes (values : Bytes.ByteString) : ByteArray := values
def append (values : ByteArray) (byte : UInt8) : ByteArray := values ++ [byte]
def clear (_ : ByteArray) : ByteArray := []
def copy (values : ByteArray) : ByteArray := values
def extend (values additional : ByteArray) : ByteArray := values ++ additional
def insert (values : ByteArray) (index : Int) (byte : UInt8) : ByteArray :=
  List.insert values index byte
def pop (values : ByteArray) (index : Int := -1) : Result (UInt8 × ByteArray) :=
  List.pop values index
def remove (values : ByteArray) (byte : UInt8) : Result ByteArray := List.remove values byte
def reverse (values : ByteArray) : ByteArray := values.reverse

def setAt (values : ByteArray) (index : Int) (byte : UInt8) : Result ByteArray :=
  List.setAt values index byte

/-- Empty replacements delete even extended slices; nonempty replacements must match their size. -/
def setSlice (values : ByteArray) (bounds : Slice.Slice) (replacement : ByteArray) : Result ByteArray :=
  if replacement.isEmpty then List.deleteSlice values bounds
  else List.setSlice values bounds replacement

theorem setSlice_uniform (values : ByteArray) (bounds : Slice.Slice) (byte : UInt8)
    (normalized : Slice.indices bounds values.length = .ok (start, stop, step))
    (extended : step ≠ 1)
    (selected : Slice.indexList bounds values.length = .ok indices) :
    setSlice values bounds (List.replicate indices.length byte) =
      .ok (indices.foldl (fun result index => result.set index byte) values) :=
by
  cases indices with
  | nil =>
      simpa [setSlice] using List.deleteSlice_empty values bounds selected
  | cons index rest =>
      simpa [setSlice] using List.setSlice_uniform values bounds byte normalized extended selected

/-- Resize in place, truncating or appending null bytes. -/
def resize (values : ByteArray) (size : Nat) : ByteArray :=
  if size ≤ values.length then values.take size
  else values ++ List.replicate (size - values.length) 0

end FormalSW.Py.Builtin.ByteArray
