import lang.py.builtin.type.core
import lang.py.builtin.type.iterator

/-! Delegation paths used by builtins when an argument is not a concrete builtin value. -/

namespace CleanXY.Py.Builtin.Function.Protocol

open CleanXY.Py.Builtin

structure IndexProtocol (α : Type u) where
  index : α → Result Int

structure AbsProtocol (α : Type u) (ResultType : Type v) where
  abs : α → Result ResultType

structure LengthProtocol (α : Type u) where
  length : α → Result Int

structure IterProtocol (α : Type u) (Element : Type v) where
  iter : α → Result (Iterator.Iterator Element)

structure AsyncIterProtocol (α : Type u) (Element : Type v) where
  aiter : α → Result (Iterator.AsyncIterator Element)

structure ReversedProtocol (α : Type u) (Element : Type v) where
  reversed : α → Result (Iterator.Iterator Element)

structure RoundProtocol (α : Type u) (ResultType : Type v) where
  round : α → Option Int → Result ResultType

structure DirProtocol (α : Type u) where
  dir : α → Result (List String)

structure BinaryNumericProtocol (α : Type u) (ResultType : Type v) where
  divmod : α → α → Result ResultType
  pow : α → α → Option α → Result ResultType

def absObject (protocol : AbsProtocol α ResultType) (object : α) : Result ResultType :=
  protocol.abs object
def indexObject (protocol : IndexProtocol α) (object : α) : Result Int := protocol.index object
def lenObject (protocol : LengthProtocol α) (object : α) : Result Nat := do
  let length ← protocol.length object
  if length < 0 then .error (.valueError "__len__() should return >= 0")
  else return length.toNat
def iterObject (protocol : IterProtocol α Element) (object : α) := protocol.iter object
def aiterObject (protocol : AsyncIterProtocol α Element) (object : α) := protocol.aiter object
def reversedObject (protocol : ReversedProtocol α Element) (object : α) := protocol.reversed object
def roundObject (protocol : RoundProtocol α ResultType) (object : α) (digits : Option Int := none) :=
  protocol.round object digits
def dirObject (protocol : DirProtocol α) (object : α) := protocol.dir object
def divmodObject (protocol : BinaryNumericProtocol α ResultType) (left right : α) :=
  protocol.divmod left right
def powObject (protocol : BinaryNumericProtocol α ResultType) (base exponent : α)
    (modulus : Option α := none) := protocol.pow base exponent modulus

end CleanXY.Py.Builtin.Function.Protocol
