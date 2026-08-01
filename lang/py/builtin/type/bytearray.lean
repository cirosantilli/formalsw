import lang.py.builtin.type.bytes

/-! Python `bytearray`: mutable byte sequences represented by pure state transitions. -/

namespace CleanXY.Py.Builtin.ByteArray

open CleanXY.Py.Builtin

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

/-- Resize in place, truncating or appending null bytes. -/
def resize (values : ByteArray) (size : Nat) : ByteArray :=
  if size ≤ values.length then values.take size
  else values ++ List.replicate (size - values.length) 0

end CleanXY.Py.Builtin.ByteArray
