import lang.py.FormalSW.HeapRuntimeCostUnpacking

open FormalSW.PyAst HeapCalls HeapCalls.Runtime
private def emptyModule : Module := { body := [] }

/-- Tuple fields are copied as references, without following their contents. -/
example : charge .bits emptyModule
    ⟨.block [.unpackStepLoop ["x", "y"] (.ref 0) 0 [] []] (fun _ => none), [],
      [.list [.ref 1], .tuple [.ref 0, .scalar (.int (2^100))]]⟩ =
    charge .bits emptyModule
    ⟨.block [.unpackStepLoop ["x", "y"] (.ref 0) 0 [] []] (fun _ => none), [],
      [.list [.ref 1], .tuple [.scalar (.int 0), .scalar (.int 0)]]⟩ := by decide

/-- Field-copy work grows with arity, while exhaustion does not unpack a value. -/
example (fields : List Mutable.Value) (names : List String) :
    unpackIteration .word [.list [.ref 1], .tuple fields] names 0 0 =
      some (fields.length+names.length+7) := by
  simp [unpackIteration, sequenceLength, PrimitiveWork.integer]; omega
example : unpackIteration .word [.list [], .tuple []] ["x", "y"] 0 0 = some 5 := rfl
example : unpackIteration .word [.list [.scalar (.int 7)]] ["x", "y"] 0 0 = none := rfl

/-- Enumerate keeps its dedicated acquisition rule. Ordinary unpacking checks
its target list before evaluating the source. -/
example : charge .word emptyModule
    ⟨.block [.forIn (.tuple [.name "i", .name "x"])
      (.call (.name "enumerate") [.name "xs"]) [] []] (fun _ => none), [], []⟩ = some 1 := rfl
example : charge .word emptyModule
    ⟨.block [.forIn (.tuple [.name "x", .constant (.int 0)]) (.name "xs") [] []]
      (fun _ => none), [], []⟩ = none := rfl

private def unpackModule : Module :=
  { body := [.functionDef "first" [⟨"xs", none, none⟩] none
    [.forIn (.tuple [.name "x", .name "y"]) (.name "xs") [] [], .return (.name "x")]] }

/-- A complete call includes acquisition, unpacking, exhaustion and the return.
The elements may alias the source or be arbitrarily large integers. -/
example (a b : Mutable.Value) : ReturnsIn .word unpackModule "first" [.ref 0]
    [.list [.ref 1], .tuple [a,b]] 26 a [.list [.ref 1], .tuple [a,b]] := by
  let env := functionEnv [⟨"xs", none, none⟩]
    [.forIn (.tuple [.name "x", .name "y"]) (.name "xs") [] [], .return (.name "x")] [.ref 0] []
  let finalEnv := assignNames env ["x", "y"] [a,b]
  have done : BlockContinuesIn .word unpackModule finalEnv
      [.unpackStepLoop ["x", "y"] (.ref 0) 1 [] []] [.list [.ref 1], .tuple [a,b]] 5
      finalEnv [.list [.ref 1], .tuple [a,b]] :=
    BlockContinuesIn.unpack_done rfl rfl BlockContinuesIn.nil
  have iteration : BlockContinuesIn .word unpackModule env
      [.unpackStepLoop ["x", "y"] (.ref 0) 0 [] []] [.list [.ref 1], .tuple [a,b]] 16
      finalEnv [.list [.ref 1], .tuple [a,b]] :=
    BlockContinuesIn.unpack_step (items := [.ref 1]) (pair := 1) (values := [a,b])
      (budget := 5) rfl rfl rfl rfl done
  have loop : BlockContinuesIn .word unpackModule env
      [.forIn (.tuple [.name "x", .name "y"]) (.name "xs") [] []] [.list [.ref 1], .tuple [a,b]] 21
      finalEnv [.list [.ref 1], .tuple [a,b]] :=
    BlockContinuesIn.for_unpack_name rfl rfl rfl iteration
  apply BlockReturnsIn.function (args := [⟨"xs", none, none⟩]) (budget := 23) rfl rfl
  exact loop.returns (BlockReturnsIn.return_value (EvaluatesIn.lookup
    (by simp [finalEnv, assignNames, setLocal])))

/-- An unevaluated local annotation can contain an undefined name. -/
example (env : HeapCalls.Env) (heap : Heap) :
    BlockContinuesIn .word emptyModule env
      [.annAssign (.name "x") (.call (.name "undefined") []) (some (.constant (.int 7)))] heap 3
      (setLocal env "x" (.scalar (.int 7))) heap :=
  BlockContinuesIn.annAssign EvaluatesIn.constant
