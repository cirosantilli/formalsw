import lang.py.FormalSW.HeapRuntimeCostSetup

open FormalSW.PyAst HeapCalls HeapCalls.Runtime

namespace GlobalsRuntimeRegression

/- Generated-shape source for:
   def helper(n): return n + OFFSET
   def solve(n): return helper(n)
   OFFSET is supplied at call entry, not embedded in either function body. -/
def args : List Arg := [⟨"n", none, none⟩]
def helperBody : List Stmt := [.return (.binOp (.name "n") .add (.name "OFFSET"))]
def solveBody : List Stmt := [.return (.call (.name "helper") [.name "n"])]
def program : Module :=
  { body := [.functionDef "helper" args none helperBody,
      .functionDef "solve" args none solveBody] }

/-- The argument shadows a global of the same name; both globals must survive. -/
def context (offset : Int) : Mutable.Globals :=
  [("OFFSET", .scalar (.int offset)), ("n", .scalar (.int 999))]

theorem helper_returns (n offset : Int) (heap : Heap) :
    ReturnsIn .word program "helper" [.scalar (.int n)] heap 10
      (.scalar (.int (n + offset))) heap (context offset) := by
  have body : BlockReturnsIn .word program
      (functionEnv args helperBody [.scalar (.int n)] (context offset))
      helperBody heap 7 (.scalar (.int (n + offset))) heap (context offset) := by
    apply BlockReturnsIn.return_value
    exact EvaluatesIn.binary (op := .add) (work := 1)
      (EvaluatesIn.lookup rfl) (EvaluatesIn.lookup rfl) rfl rfl
  exact BlockReturnsIn.function (args := args) (body := helperBody) rfl rfl body

/-- Entering the helper must carry the same globals as entering solve. -/
theorem solve_returns (n offset : Int) (heap : Heap) :
    ReturnsIn .word program "solve" [.scalar (.int n)] heap 17
      (.scalar (.int (n + offset))) heap (context offset) := by
  have body : BlockReturnsIn .word program
      (functionEnv args solveBody [.scalar (.int n)] (context offset))
      solveBody heap 14 (.scalar (.int (n + offset))) heap (context offset) := by
    apply BlockReturnsIn.return_value
    exact EvaluatesIn.call_single (EvaluatesIn.lookup rfl) (helper_returns n offset heap)
  exact BlockReturnsIn.function (args := args) (body := solveBody) rfl rfl body

/-- Include the terminal transition, checking the value, globals, heap and anchors. -/
theorem solve_finishes (n offset : Int) (heap : Heap) :
    ∃ cost, RuntimeCost.Finishes
      (HeapCalls.call program "solve" [.scalar (.int n)] heap (context offset)).execution.step
      (charge .word program)
      (HeapCalls.call program "solve" [.scalar (.int n)] heap (context offset)).execution.initial
      cost (.ok ⟨.ok (.scalar (.int (n + offset))), context offset, heap, heap.length⟩) ∧
      cost ≤ 18 := by
  obtain ⟨cost, steps, paid⟩ := solve_returns n offset heap heap.length []
  have terminal : RuntimeCost.Finishes
      (HeapCalls.step (globals := context offset) program heap.length) (charge .word program)
      ⟨.value (.scalar (.int (n + offset))), [], heap⟩ 1
      (.ok ⟨.ok (.scalar (.int (n + offset))), context offset, heap, heap.length⟩) :=
    .done rfl rfl
  refine ⟨cost + 1, steps.finishes terminal, ?_⟩
  simp only [potential] at paid
  omega

theorem solve_timeBound (n offset : Int) (heap : Heap) :
    TimeBound .word program "solve" [.scalar (.int n)] heap 18
      (globals := context offset) := by
  obtain ⟨cost, run, bounded⟩ := solve_finishes n offset heap
  exact ⟨cost, _, run, bounded⟩

example : context 7 ≠ context (-3) := by decide

example : TimeBound .word program "solve" [.scalar (.int 5)] [] 18
    (globals := context 7) := solve_timeBound 5 7 []

example : TimeBound .word program "solve" [.scalar (.int 5)] [] 18
    (globals := context (-3)) := solve_timeBound 5 (-3) []

example : (HeapCalls.call program "solve" [.scalar (.int 5)] [] (context 7)).Finishes
    ⟨.ok (.scalar (.int 12)), context 7, [], 0⟩ := by
  obtain ⟨_, run, _⟩ := solve_finishes 5 7 []
  exact run.execution

example : (HeapCalls.call program "solve" [.scalar (.int 5)] [] (context (-3))).Finishes
    ⟨.ok (.scalar (.int 2)), context (-3), [], 0⟩ := by
  obtain ⟨_, run, _⟩ := solve_finishes 5 (-3) []
  exact run.execution

def legacyProgram : Module :=
  { body := [.functionDef "identity" args none [.return (.name "n")]] }

/-- Old source proofs omit the optional globals argument throughout. -/
theorem legacy_returns (n : Int) :
    ReturnsIn .word legacyProgram "identity" [.scalar (.int n)] [] 5 (.scalar (.int n)) [] := by
  apply BlockReturnsIn.function (args := args) (budget := 2) rfl rfl
  exact BlockReturnsIn.return_value (EvaluatesIn.lookup rfl)

example (n : Int) : TimeBound .word legacyProgram "identity" [.scalar (.int n)] [] 6 := by
  exact ReturnsIn.timeBound_append (extra := []) (legacy_returns n)

end GlobalsRuntimeRegression
