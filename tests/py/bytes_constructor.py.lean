import «.formalsw».tests.py.«bytes_constructor.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.bytes_constructor
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := BytesConstructorAst.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)

theorem empty.result (n : Int) (heap : Mutable.Heap) :
    ReturnsValue program "empty" [number n] heap (.scalar (.bytes [])) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.builtin .nil rfl

theorem copy.result (value : List UInt8) (heap : Mutable.Heap) :
    ReturnsValue program "copy" [.scalar (.bytes value)] heap (.scalar (.bytes value)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil) rfl

/-- A dynamic three-integer tuple is converted in place, with no mutable buffer. -/
theorem normalized.result (n : Int) (heap : Mutable.Heap) :
    ReturnsValue program "normalized" [number n] heap
      (.scalar (.bytes [UInt8.ofNat (n % 256).toNat, 0, 255]))
      (heap ++ [.tuple [number (n % 256), number 0, number 255]]) := by
  have lower : 0 ≤ n % 256 := Int.emod_nonneg n (by decide)
  have upper : n % 256 < 256 := Int.emod_lt_of_pos n (by decide)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.builtin (.cons
    (Evaluates.tuple (.cons
      (Evaluates.binary (value := number (n % 256)) (Evaluates.lookup rfl)
        (Evaluates.constant (value := .int 256)) rfl)
      (.cons (Evaluates.constant (value := .int 0)) (.cons (Evaluates.constant (value := .int 255)) .nil)))
      (by simp)) .nil)
  change Mutable.bytes [.ref heap.length] (heap ++ [.tuple [number (n % 256), number 0, number 255]]) = _
  apply Mutable.bytes_tuple (items := [number (n % 256), number 0, number 255])
  · simp
  · simp [Mutable.bytesElement, Mutable.byte, Mutable.integer, lower, upper]

theorem empty.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "empty" [.int n]).Returns :=
  ReturnsValue.scalar_returns (empty.result n [])

theorem empty.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "empty" [.int n]).Supported := (empty.«Returns» n).supported

theorem copy.«Returns» (value : List UInt8) :
    (HeapCalls.scalarFunction program "copy" [.bytes value]).Returns :=
  ReturnsValue.scalar_returns (copy.result value [])

theorem copy.«Supported» (value : List UInt8) :
    (HeapCalls.scalarFunction program "copy" [.bytes value]).Supported := (copy.«Returns» value).supported

theorem normalized.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "normalized" [.int n]).Returns :=
  ReturnsValue.scalar_returns (normalized.result n [])

theorem normalized.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "normalized" [.int n]).Supported := (normalized.«Returns» n).supported

end tests.py.bytes_constructor
