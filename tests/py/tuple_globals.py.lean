import «.formalsw».tests.py.«tuple_globals.py.ast»
import FormalSW

namespace tests.py.tuple_globals
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := TupleGlobalsAst.module

/-- The entry tuple can have any contents and any address in the caller heap. -/
theorem read.result (heap : Mutable.Heap) (address : Nat) :
    ReturnsValue program "read" [] heap (.ref address) heap [("TABLE", .ref address)] := by
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.lookup rfl)

theorem read.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid)
    (_typed : Mutable.Value.HasContainerType heap (.ref address) (.tupleOf (.scalar "int"))) :
    (HeapCalls.call program "read" [] heap [("TABLE", .ref address)]).Returns :=
  (read.result heap address).returns

theorem read.«ReturnType» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid)
    (typed : Mutable.Value.HasContainerType heap (.ref address) (.tupleOf (.scalar "int"))) :
    (HeapCalls.call program "read" [] heap [("TABLE", .ref address)]).ReturnContainerType
      (.tupleOf (.scalar "int")) :=
  .inr ⟨.ref address, _, heap, heap.length, (read.result heap address).finishes, typed⟩

theorem read.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid)
    (typed : Mutable.Value.HasContainerType heap (.ref address) (.tupleOf (.scalar "int"))) :
    (HeapCalls.call program "read" [] heap [("TABLE", .ref address)]).Supported :=
  (read.«Returns» heap address valid typed).supported

/-- The alias declaration does not force the two call-entry references to coincide. -/
theorem same.result (heap : Mutable.Heap) (alias table : Nat) :
    ReturnsValue program "same" [] heap (.scalar (.bool (table == alias))) heap
      [("ALIAS", .ref alias), ("TABLE", .ref table)] := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.builtin (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) rfl

theorem same.«Returns» (heap : Mutable.Heap) (alias table : Nat)
    (_valid : heap.Valid)
    (_aliasTyped : Mutable.Value.HasContainerType heap (.ref alias) (.tupleOf (.scalar "int")))
    (_tableTyped : Mutable.Value.HasContainerType heap (.ref table) (.tupleOf (.scalar "int"))) :
    (HeapCalls.call program "same" [] heap [("ALIAS", .ref alias), ("TABLE", .ref table)]).Returns :=
  (same.result heap alias table).returns

theorem same.«Supported» (heap : Mutable.Heap) (alias table : Nat)
    (valid : heap.Valid)
    (aliasTyped : Mutable.Value.HasContainerType heap (.ref alias) (.tupleOf (.scalar "int")))
    (tableTyped : Mutable.Value.HasContainerType heap (.ref table) (.tupleOf (.scalar "int"))) :
    (HeapCalls.call program "same" [] heap [("ALIAS", .ref alias), ("TABLE", .ref table)]).Supported :=
  (same.«Returns» heap alias table valid aliasTyped tableTyped).supported

end tests.py.tuple_globals
