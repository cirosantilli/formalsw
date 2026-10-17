import lang.py.builtin.type.bytes

/-! A typed, multidimensional view over an exporter buffer. -/

namespace FormalSW.Py.Builtin.MemoryView

open FormalSW.Py.Builtin

/-- Buffer metadata and a logical C-order byte snapshot. -/
structure MemoryView where
  exporterId : Nat
  data : Bytes.ByteString
  readonly : Bool
  format : String := "B"
  itemSize : Nat := 1
  shape : List Nat := []
  strides : List Int := []
  suboffsets : List Int := []
  released : Bool := false
deriving Repr, DecidableEq

def create (exporterId : Nat) (data : Bytes.ByteString) (readonly : Bool := false) : MemoryView :=
  { exporterId, data, readonly, shape := [data.length], strides := [1] }

def nbytes (view : MemoryView) : Nat := view.data.length
def ndim (view : MemoryView) : Nat := view.shape.length
def itemCount (view : MemoryView) : Nat :=
  if view.itemSize = 0 then 0 else nbytes view / view.itemSize

private def ensureOpen (view : MemoryView) : Result Unit :=
  if view.released then .error (.valueError "operation forbidden on released memoryview object")
  else .ok ()

def toBytes (view : MemoryView) : Result Bytes.ByteString := do
  ensureOpen view
  return view.data

def hex (view : MemoryView) : Result String := Bytes.hex <$> toBytes view

/-- Logical element values. The generic model interprets each item as an unsigned big-endian int. -/
private def chunksFuel : Nat → Nat → List α → List (List α)
  | 0, _, _ => []
  | _, 0, _ => []
  | _, _, [] => []
  | fuel + 1, size, values =>
      values.take size :: chunksFuel fuel size (values.drop size)

private def unsignedItem (bytes : Bytes.ByteString) : Nat :=
  bytes.foldl (fun value byte => value * 256 + byte.toNat) 0

def toList (view : MemoryView) : Result (List Nat) := do
  ensureOpen view
  if view.itemSize = 0 then .error (.valueError "memoryview itemsize cannot be zero")
  else return (chunksFuel (itemCount view) view.itemSize view.data).map unsignedItem

def toReadonly (view : MemoryView) : Result MemoryView := do
  ensureOpen view
  return { view with readonly := true }

def release (view : MemoryView) : MemoryView := { view with released := true }

/-- Cast changes the logical format/shape without changing the underlying bytes. -/
def cast (view : MemoryView) (format : String) (itemSize : Nat)
    (shape : Option (List Nat) := none) : Result MemoryView := do
  ensureOpen view
  if itemSize = 0 || nbytes view % itemSize != 0 then
    .error (.typeError "memoryview: length is not a multiple of itemsize")
  else
    let targetShape := shape.getD [nbytes view / itemSize]
    if targetShape.foldl (· * ·) 1 * itemSize != nbytes view then
      .error (.typeError "memoryview: product(shape) * itemsize != buffer size")
    else
      .ok { view with
        format := format
        itemSize := itemSize
        shape := targetShape
        strides := []
        suboffsets := [] }

def equivalent (left right : MemoryView) : Result Bool := do
  ensureOpen left
  ensureOpen right
  let leftValues ← toList left
  let rightValues ← toList right
  return left.format == right.format && left.shape == right.shape && leftValues == rightValues

def count (view : MemoryView) (value : Nat) : Result Nat := do
  let values ← toList view
  return values.foldl (fun total item => if item = value then total + 1 else total) 0

def index? (view : MemoryView) (value : Nat) : Result (Option Nat) := do
  let values ← toList view
  return values.findIdx? (· = value)

def cContiguous (view : MemoryView) : Bool := view.strides.isEmpty || ndim view ≤ 1
def fContiguous (view : MemoryView) : Bool := view.strides.isEmpty || ndim view ≤ 1
def contiguous (view : MemoryView) : Bool := cContiguous view || fContiguous view

/-- Context-manager entry returns the live view. -/
def enter (view : MemoryView) : Result MemoryView := ensureOpen view *> pure view

/-- Context-manager exit releases the view and does not suppress exceptions. -/
def exit (view : MemoryView) : Bool × MemoryView := (false, release view)

example : nbytes (create 1 [1, 2, 3]) = 3 := rfl
example : toList (create 1 [1, 2]) = .ok [1, 2] := rfl

end FormalSW.Py.Builtin.MemoryView
