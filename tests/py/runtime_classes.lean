import lang.py.FormalSW.HeapRuntimeCostClasses

open FormalSW.PyAst HeapCalls HeapCalls.Runtime
private def initArgs : List Arg := [⟨"self", none, none⟩, ⟨"value", none, some (.int 7)⟩]
private def initBody : List Stmt :=
  [.annAssign (.attribute (.name "self") "x") (.call (.name "undefined") []) (some (.name "value"))]
private def methodArgs : List Arg := [⟨"self", none, none⟩, ⟨"n", none, some (.int 11)⟩]
private def methodBody : List Stmt := [.return (.name "n")]
private def program : Module :=
  { body := [.classDef "Box" [.functionDef "__init__" initArgs none initBody,
      .functionDef "echo" methodArgs none methodBody]], classOrigins := [("Box", "example")] }
private def box : Mutable.Object := .instance "example" "Box" [("x", .scalar (.int 7))]

/-- The initializer receives implicit self and its default argument. Its local
annotation is not evaluated, and the stored field is visible on return. -/
example (heap : Heap) : ReturnsIn .word program "Box" [] heap 16 (.ref heap.length) (heap ++ [box]) := by
  apply ReturnsIn.constructor (args := initArgs) (body := initBody) (budget := 10) rfl rfl rfl rfl rfl
  have assigned : BlockContinuesIn .word program (functionEnv initArgs initBody [.ref heap.length, .scalar (.int 7)] [])
      initBody (heap ++ [.instance "example" "Box" []]) 9
      (functionEnv initArgs initBody [.ref heap.length, .scalar (.int 7)] []) (heap ++ [box]) := by
    apply BlockContinuesIn.annAttribute (cr := 1) (ct := 1) (work := 2)
      (EvaluatesIn.lookup rfl) (EvaluatesIn.lookup rfl)
    · have written :=
        (Mutable.writeField_result (heap := heap ++ [.instance "example" "Box" []]) (address := heap.length)
          (origin := "example") (className := "Box") (fields := [])
          (name := "x") (value := .scalar (.int 7)) (by simp) (by decide))
      rw [List.set_append_right _ _ (Nat.le_refl _)] at written
      simpa only [Nat.sub_self, List.set, Mutable.putField, box] using written
    · simp [RecordWork.write, RecordWork.lookup]
    · simp [heapPotential, objectPotential, box]
  exact assigned.returns BlockReturnsIn.fallthrough

/-- Explicit argument count excludes self; a method default is still completed. -/
example : EvaluatesIn .word program (fun _ => some (.ref 0))
    (.call (.attribute (.name "box") "echo") []) [box] 16 (.scalar (.int 11)) [box] := by
  have body : BlockReturnsIn .word program
      (functionEnv methodArgs methodBody [.ref 0, .scalar (.int 11)] []) methodBody
      [box] 2 (.scalar (.int 11)) [box] :=
    BlockReturnsIn.return_value (EvaluatesIn.lookup rfl)
  have method : MethodReturnsIn .word program (.ref 0) methodArgs methodBody [] [box] 6 (.scalar (.int 11)) [box] :=
    MethodReturnsIn.of_body rfl body
  apply EvaluatesIn.method (ca := 0) (cb := 6) (work := 7) rfl (by decide)
  · rfl
  · rfl
  · exact ArgumentsIn.nil
  · exact method

/-- Live shadowing fields and mismatched nominal class identities are rejected. -/
example : RecordWork.method program [.instance "example" "Box" [("echo", .scalar (.int 0))]] (.ref 0) "echo" = none := rfl
example : RecordWork.method program [.instance "other" "Box" []] (.ref 0) "echo" = none := rfl

/-- Field updates charge traversal/rebuilding independently of referent size. -/
example (count : Nat) : RecordWork.write [.instance "example" "Box" (List.replicate count ("x", .ref 0))] (.ref 0) "y" =
    some (4*count+2) := by
  have lengths : "x".length + "y".length + 1 = 3 := by decide
  simp [RecordWork.write, RecordWork.lookup, lengths, Nat.mul_comm]; omega
example : RecordWork.write [.dataInstance "example" "Box" true ["x"] [("x", .scalar (.int 7))]] (.ref 0) "x" = none := rfl
example : RecordWork.write [box] (.ref 0) "__dict__" = none := rfl

/-- A non-None initializer result still raises TypeError at the priced boundary. -/
example : step program 0 ⟨.value (.scalar (.int 5)), [.initialized 0], [box]⟩ =
    done 0 [box] (.error {typeName := "TypeError", args := []}) := rfl
example : charge .word program ⟨.value (.scalar (.int 5)), [.initialized 0], [box]⟩ = some 1 := rfl
