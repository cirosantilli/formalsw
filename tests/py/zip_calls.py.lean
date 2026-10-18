import «.formalsw».tests.py.«zip_calls.py.ast»
import FormalSW

namespace tests.py.zip_calls
open FormalSW.PyAst
private abbrev program := ZipCallsAst.module
private def inputs (heap : Mutable.Heap) (n : Int) : Mutable.Heap :=
  heap ++ [.list [.scalar (.int n)], .list [.scalar (.int (n + 1))]]
private def fields (n : Int) : List Mutable.Value := [.scalar (.int n), .scalar (.int (n + 1))]
private def finished (heap : Mutable.Heap) (n : Int) : Mutable.Heap :=
  inputs heap n ++ [.tuple (fields n)]
private def sources (heap : Mutable.Heap) : List SequenceSource :=
  [.ref heap.length, .ref (heap.length + 1)]
private abbrev arguments : List Expr :=
  [.list [.name "n"], .list [.binOp (.name "n") .add (.constant (.int 1))]]

private theorem arguments.result (heap : Mutable.Heap) (env : HeapCalls.Env) (n : Int)
    (getN : env "n" = some (.scalar (.int n))) :
    HeapCalls.Evaluates.Arguments program env arguments heap
      [.ref heap.length, .ref (heap.length + 1)] (inputs heap n) := by
  have first : HeapCalls.Evaluates program env (.list [.name "n"]) heap (.ref heap.length)
      (heap ++ [.list [.scalar (.int n)]]) :=
    HeapCalls.Evaluates.list (.cons (.lookup getN) .nil)
  have second : HeapCalls.Evaluates program env (.list [.binOp (.name "n") .add (.constant (.int 1))])
      (heap ++ [.list [.scalar (.int n)]]) (.ref (heap.length + 1)) (inputs heap n) := by
    have evaluated := HeapCalls.Evaluates.list (module := program) (globals := []) (HeapCalls.Evaluates.Arguments.cons
      (HeapCalls.Evaluates.binary (heap := heap ++ [.list [.scalar (.int n)]])
        (op := .add) (.lookup getN) (HeapCalls.Evaluates.constant (value := .int 1)) rfl) .nil)
    simpa [inputs, List.append_assoc] using evaluated
  exact .cons first (.cons second .nil)

private theorem captured (heap : Mutable.Heap) (n : Int) :
    HeapCalls.zipSources [.ref heap.length, .ref (heap.length + 1)] (inputs heap n) =
      some (.ok (sources heap), inputs heap n) := by
  simp [HeapCalls.zipSources, Mutable.sequence, inputs, sources, HeapCalls.sequenceSource,
    List.mapM, List.mapM.loop, Except.map]

private theorem fetched (heap : Mutable.Heap) (n : Int) :
    HeapCalls.zipItem (sources heap) 0 (inputs heap n) = some (.ok (some (fields n)), inputs heap n) := by
  simp [HeapCalls.zipItem, HeapCalls.zipFields, HeapCalls.sequenceValue, Mutable.sequence, inputs, sources, fields, Except.map]

private theorem exhausted (heap : Mutable.Heap) (n : Int) :
    HeapCalls.zipItem (sources heap) 1 (finished heap n) = some (.ok none, finished heap n) := by
  simp [HeapCalls.zipItem, HeapCalls.zipFields, HeapCalls.sequenceValue, Mutable.sequence,
    inputs, sources, finished, List.append_assoc]

private theorem tuple_sequence (heap : Mutable.Heap) (n : Int) :
    Mutable.sequence (.ref (inputs heap n).length) (finished heap n) =
      some (.ok (fields n), finished heap n) := by simp [finished, Mutable.sequence]

private theorem allocate (heap : Mutable.Heap) (n : Int) :
    Mutable.allocateTuple (fields n) (inputs heap n) =
      some (.ok (.ref (inputs heap n).length), finished heap n) := rfl

private theorem pair_sum.result (n : Int) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "pair_sum" [.scalar (.int n)] heap
      (.scalar (.int (2 * n + 1))) (finished heap n) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.sum_generator_targets_zip
    (arguments.result heap _ n rfl) (captured heap n) .constant rfl
  apply HeapCalls.BlockReturns.zip_step (fetched heap n) (allocate heap n)
  apply HeapCalls.BlockReturns.unpack (items := fields n) (afterUnpack := finished heap n)
    rfl (HeapCalls.Evaluates.lookup rfl) (tuple_sequence heap n) rfl
  apply HeapCalls.BlockReturns.assign (value := .scalar (.int (n + (n + 1)))) (middle := finished heap n)
  · exact HeapCalls.Evaluates.binary (.lookup rfl)
      (HeapCalls.Evaluates.binary (.lookup rfl) (.lookup rfl) rfl)
      (by simp [Mutable.binary, scalarBinary])
  · apply HeapCalls.BlockReturns.zip_done (exhausted heap n)
    apply HeapCalls.BlockReturns.return_value
    apply HeapCalls.Evaluates.lookup
    simp [HeapCalls.setLocal]
    omega

private theorem first_pair.result (n : Int) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "first_pair" [.scalar (.int n)] heap
      (.scalar (.int (2 * n + 1))) (finished heap n) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.for_zip (arguments.result heap _ n rfl) (captured heap n)
  apply HeapCalls.BlockReturns.zip_step (fetched heap n) (allocate heap n)
  apply HeapCalls.BlockReturns.unpack (items := fields n) (afterUnpack := finished heap n)
    rfl (HeapCalls.Evaluates.lookup rfl) (tuple_sequence heap n) rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.binary (.lookup rfl) (.lookup rfl)
  simp [Mutable.binary, scalarBinary]
  omega

theorem pair_sum.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "pair_sum" [.int n]).Returns :=
  (pair_sum.result n []).scalar_returns

theorem pair_sum.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "pair_sum" [.int n]).Supported :=
  (pair_sum.«Returns» n).supported

theorem first_pair.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "first_pair" [.int n]).Returns :=
  (first_pair.result n []).scalar_returns

theorem first_pair.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "first_pair" [.int n]).Supported :=
  (first_pair.«Returns» n).supported

end tests.py.zip_calls
