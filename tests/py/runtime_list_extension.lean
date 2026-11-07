import lang.py.FormalSW.HeapRuntimeCostListExtension
import lang.py.FormalSW.HeapRuntimeCostListCopies

open FormalSW.PyAst HeapCalls HeapCalls.Runtime
private def emptyModule : Module := { body := [] }

/-- A full receiver pays to copy its existing contents on the next append. -/
example : charge .word emptyModule
    ⟨.value (.ref 1), [.binaryRight .add (.ref 0) true],
      [.list (List.replicate 8 (.ref 0)), .list [.scalar (.int 7)]]⟩ = some 12 := by decide
example : charge .word emptyModule
    ⟨.value (.ref 1), [.binaryRight .add (.ref 0) true],
      [.list (List.replicate 9 (.ref 0)), .list [.scalar (.int 7)]]⟩ = some 4 := by decide

/-- Copying references does not inspect integer widths or follow cycles. -/
example : charge .bits emptyModule
    ⟨.value (.ref 1), [.binaryRight .add (.ref 0) true],
      [.list (List.replicate 8 (.ref 0)), .list [.scalar (.int (2^100))]]⟩ = some 12 := by decide

/-- Self-extension snapshots the original contents and keeps the same receiver. -/
example (items : List Mutable.Value) (arithmetic : PrimitiveWork.Arithmetic) :
    BlockContinuesIn arithmetic emptyModule (fun _ => some (.ref 0))
      [.augAssign (.name "xs") .add (.name "xs")] [.list items]
      (4*items.length+7) (setLocal (fun _ => some (.ref 0)) "xs" (.ref 0))
      [.list (items ++ items)] := by
  exact (BlockContinuesIn.augAssign_list (items := items) (additional := items) (address := 0) (source := 0) rfl (EvaluatesIn.lookup rfl) rfl rfl).mono (by omega)

/-- Effects inside the RHS happen before the receiver contents are read.
The nested extension is executed, then the outer extension uses the grown list. -/
private def grow : Module :=
  { body := [.functionDef "grow" [⟨"xs", none, none⟩] none
    [.augAssign (.name "xs") .add (.name "xs"), .return (.name "xs")]] }

example (items : List Mutable.Value) :
    BlockContinuesIn .word grow (fun _ => some (.ref 0))
      [.augAssign (.name "xs") .add (.call (.name "grow") [.name "xs"])] [.list items]
      (12*items.length+21) (setLocal (fun _ => some (.ref 0)) "xs" (.ref 0))
      [.list ((items ++ items) ++ (items ++ items))] := by
  have called : ReturnsIn .word grow "grow" [.ref 0] [.list items]
      (1+1+1+(4*items.length+9)) (.ref 0) [.list (items ++ items)] := by
    apply BlockReturnsIn.function (args := [⟨"xs", none, none⟩]) (budget := 4*items.length+9) rfl rfl
    have extended := BlockContinuesIn.augAssign_list (arithmetic := .word) (module := grow)
      (items := items) (additional := items) (address := 0) (source := 0) (name := "xs")
      (expression := .name "xs") (heap := [.list items]) (env := functionEnv [⟨"xs", none, none⟩]
        [.augAssign (.name "xs") .add (.name "xs"), .return (.name "xs")] [.ref 0] [])
      rfl (EvaluatesIn.lookup rfl) rfl rfl
    exact (extended.returns (BlockReturnsIn.return_value (EvaluatesIn.lookup rfl))).mono (by omega)
  have rhs := EvaluatesIn.call (env := fun _ => some (.ref 0)) (expressions := [.name "xs"])
    (ArgumentsIn.cons (EvaluatesIn.lookup rfl) ArgumentsIn.nil) called
  exact (BlockContinuesIn.augAssign_list (items := items ++ items) (additional := items ++ items) (address := 0) (source := 0) rfl rhs rfl rfl).mono (by simp; omega)

/-- A grow-only tariff cannot be borrowed for shrinking or unsupported sources. -/
example : charge .word emptyModule
    ⟨.value (.scalar (.int 0)), [.binaryRight .mult (.ref 0) true], [.list [.scalar (.int 1)]]⟩ = none := rfl
example : charge .word emptyModule
    ⟨.value (.ref 1), [.binaryRight .add (.ref 0) true], [.list [], .set []]⟩ = none := rfl
