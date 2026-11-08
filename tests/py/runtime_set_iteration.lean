import lang.py.FormalSW.SetRuntimeCostLoops

open FormalSW.PyAst
namespace SetRuntimeRegression

private def program : Module :=
  { body := [.functionDef "pick" [⟨"xs", none, none⟩] none
    [.forIn (.name "x") (.name "xs") [.return (.name "x")] [], .return (.constant (.int 0))]] }

private def heap : Mutable.Heap := [.set [.int 10, .int 20]]
private def entry : HeapCalls.Env := HeapCalls.functionEnv [⟨"xs", none, none⟩]
  [.forIn (.name "x") (.name "xs") [.return (.name "x")] [], .return (.constant (.int 0))]
  [.ref 0] []

/-- Returning the first member depends on order, but one budget covers every
schedule. This includes function entry, acquisition, the iterator and return. -/
theorem pick_bound : SetCalls.Runtime.TimeBound .word program "pick" [.ref 0] heap 19 := by
  intro choices
  let items : List Constant := [.int 10, .int 20]
  let index := choices 0 % 2
  have inside : index < items.length := Nat.mod_lt _ (by decide)
  let item := items[index]
  have selected : items[choices 0 % items.length]? = some item :=
    List.getElem?_eq_getElem inside
  have head : HeapCalls.Runtime.Reaches .word program 1
      ⟨.operation (.call "pick") [.ref 0], [], heap⟩ 5
      ⟨.value (.ref 0), [.sequence "x" [.return (.name "x")] []
        [.return (.constant (.int 0))] entry], heap⟩ := by
    have enter := HeapCalls.Runtime.advance (globals := []) (arithmetic := .word)
      (module := program) (anchors := 1)
      (initial := ⟨.operation (.call "pick") [.ref 0], [], heap⟩) rfl rfl rfl
    have acquire := HeapCalls.Runtime.advance (globals := []) (arithmetic := .word)
      (module := program) (anchors := 1)
      (initial := ⟨.block [.forIn (.name "x") (.name "xs") [.return (.name "x")] [],
        .return (.constant (.int 0))] entry, [], heap⟩) rfl rfl rfl
    exact enter.trans (acquire.trans (HeapCalls.Runtime.EvaluatesIn.lookup
      (module := program) (arithmetic := .word) (env := entry) (heap := heap)
      (name := "xs") rfl 1 _))
  have acquire := SetCalls.Runtime.acquire (globals := []) (arithmetic := .word)
    (module := program) (anchors := 1) (choices := choices) (used := 0)
    (heap := heap) (address := 0) (items := items) (name := "x")
    (body := [.return (.name "x")]) (otherwise := [])
    (following := [.return (.constant (.int 0))]) (env := entry) (stack := []) rfl
  have chosen := SetCalls.Runtime.iterator_step (globals := []) (module := program)
    (anchors := 1) (choices := choices) (used := 0) (heap := heap) (address := 0)
    (original := items) (remaining := items) (current := items) (item := item)
    (name := "x") (body := [.return (.name "x")]) (otherwise := [])
    (following := [.return (.constant (.int 0))]) (env := entry) (stack := [])
    rfl rfl (by decide) selected
  have returned := HeapCalls.Runtime.BlockReturnsIn.return_value
    (following := [Calls.loopContinuation [.return (.name "x")]
      (.setStepLoop "x" 0 items (items.eraseIdx index) [.return (.name "x")] []),
      .return (.constant (.int 0))])
    (HeapCalls.Runtime.EvaluatesIn.lookup (globals := []) (module := program) (arithmetic := .word)
      (heap := heap) (env := HeapCalls.setLocal entry "x" (.scalar item)) (name := "x") rfl)
  have run := (((SetCalls.Runtime.lift_heap (choices := choices) (used := 0) head).trans acquire).trans chosen).trans
    (SetCalls.Runtime.lift_heap (choices := choices) (used := 1) (returned 1 []))
  exact SetCalls.Runtime.trace_timeBound_append (extra := []) run

/-- A change in size still invalidates the iterator; a tariff cannot turn that
exception into successful enumeration. -/
example : SetCalls.step program 1 (fun _ => 0)
    ⟨⟨.block [.setStepLoop "x" 0 [.int 10] [.int 10] [] []] (fun _ => none), [], heap⟩, 0⟩ =
    .done (.ok ⟨.error { typeName := "RuntimeError", args := [] }, [], heap, 1⟩) := rfl

example : SetCalls.Runtime.charge .word program
    ⟨⟨.block [.keySetStepLoop "x" 0 1 [.ref 1] [] []] (fun _ => none), [], heap⟩, 0⟩ = none := rfl

end SetRuntimeRegression
