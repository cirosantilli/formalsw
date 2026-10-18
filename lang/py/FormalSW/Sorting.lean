import lang.py.FormalSW.Runtime

namespace FormalSW.PyAst

/-- Merge with comparisons that may return, throw, diverge, or be unsupported.
Each successful comparison removes one head; it does not consume an arbitrary
fuel allowance or assume that the comparison itself terminates.
-/
def mergeExecution (compare : Value → Value → Execution Bool)
    (left right : List Value) : Execution (List Value) :=
  match left, right with
  | [], right => Execution.pure right
  | left, [] => Execution.pure left
  | a :: left, b :: right =>
      (compare a b).bind fun chooseLeft =>
        if chooseLeft then
          (mergeExecution compare left (b :: right)).bind fun result =>
            Execution.pure (a :: result)
        else
          (mergeExecution compare (a :: left) right).bind fun result =>
            Execution.pure (b :: result)
termination_by left.length + right.length
decreasing_by all_goals simp_wf

/-- Splitting a finite list terminates; executing its comparisons need not. -/
def mergeSortExecution (compare : Value → Value → Execution Bool)
    (values : List Value) : Execution (List Value) :=
  if short : values.length ≤ 1 then Execution.pure values
  else
    let middle := values.length / 2
    (mergeSortExecution compare (values.take middle)).bind fun left =>
      (mergeSortExecution compare (values.drop middle)).bind fun right =>
        mergeExecution compare left right
termination_by values.length
decreasing_by
  all_goals
    simp_wf
    have positive : 0 < values.length := by omega
    have half_lt := Nat.div_lt_self positive (by decide : 1 < 2)
    have _half_positive : 0 < values.length / 2 := by omega
    omega

theorem mergeSort_pair_not_halts (compare : Value → Value → Execution Bool) (a b : Value)
    (loops : ¬ (compare a b).Halts) : ¬ (mergeSortExecution compare [a, b]).Halts := by
  intro h
  rw [mergeSortExecution] at h
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff,
    ↓reduceDIte, Nat.reduceDiv, List.take_succ_cons, List.take_zero,
    List.drop_succ_cons, List.drop_zero] at h
  have left : Finishes (mergeSortExecution compare [a]).step
      (mergeSortExecution compare [a]).initial (.ok [a]) := by
    rw [mergeSortExecution]
    exact .done rfl
  have right : Finishes (mergeSortExecution compare [b]).step
      (mergeSortExecution compare [b]).initial (.ok [b]) := by
    rw [mergeSortExecution]
    exact .done rfl
  have afterLeft := Execution.halts_continuation_of_bind
    (continuation := fun left => (mergeSortExecution compare [b]).bind fun right =>
      mergeExecution compare left right) left h
  have merged := Execution.halts_continuation_of_bind
    (continuation := mergeExecution compare [a]) right afterLeft
  rw [mergeExecution] at merged
  exact loops (Execution.halts_of_bind merged)

theorem mergeExecution_returns (compare : Value → Value → Execution Bool)
    (left right : List Value)
    (safe : ∀ a ∈ left, ∀ b ∈ right, (compare a b).Returns) :
    ∃ result, Finishes (mergeExecution compare left right).step
      (mergeExecution compare left right).initial (.ok result) ∧
      ∀ value ∈ result, value ∈ left ∨ value ∈ right := by
  cases hl : left with
  | nil =>
      refine ⟨right, ?_, by simp⟩
      rw [mergeExecution]
      exact .done rfl
  | cons a left =>
      cases hr : right with
      | nil =>
          refine ⟨a :: left, ?_, by simp⟩
          rw [mergeExecution]
          · exact .done rfl
          · simp
      | cons b right =>
          simp only [hl, hr] at safe
          obtain ⟨choice, compared⟩ := safe a (by simp) b (by simp)
          cases choice with
          | true =>
              obtain ⟨result, finished, members⟩ := mergeExecution_returns compare left (b :: right)
                (by intro x hx y hy; exact safe x (by simp [hx]) y hy)
              refine ⟨a :: result, ?_, ?_⟩
              · rw [mergeExecution]
                exact Execution.finishes_bind_ok compared
                  (Execution.finishes_bind_ok finished (.done rfl))
              · intro value member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact .inl (by simp)
                · rcases members value member with h | h
                  · exact .inl (by simp [h])
                  · exact .inr h
          | false =>
              obtain ⟨result, finished, members⟩ := mergeExecution_returns compare (a :: left) right
                (by intro x hx y hy; exact safe x hx y (by simp [hy]))
              refine ⟨b :: result, ?_, ?_⟩
              · rw [mergeExecution]
                exact Execution.finishes_bind_ok compared
                  (Execution.finishes_bind_ok finished (.done rfl))
              · intro value member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact .inr (by simp)
                · rcases members value member with h | h
                  · exact .inl h
                  · exact .inr (by simp [h])
termination_by left.length + right.length
decreasing_by all_goals simp_all [List.length_cons]

theorem mergeSortExecution_returns (compare : Value → Value → Execution Bool)
    (values : List Value)
    (safe : ∀ a ∈ values, ∀ b ∈ values, (compare a b).Returns) :
    ∃ result, Finishes (mergeSortExecution compare values).step
      (mergeSortExecution compare values).initial (.ok result) ∧
      ∀ value ∈ result, value ∈ values := by
  by_cases short : values.length ≤ 1
  · refine ⟨values, ?_, by simp⟩
    rw [mergeSortExecution, dif_pos short]
    exact .done rfl
  · let middle := values.length / 2
    obtain ⟨left, left_done, left_mem⟩ :=
      mergeSortExecution_returns compare (values.take middle) (by
        intro a ha b hb
        exact safe a (List.mem_of_mem_take ha) b (List.mem_of_mem_take hb))
    obtain ⟨right, right_done, right_mem⟩ :=
      mergeSortExecution_returns compare (values.drop middle) (by
        intro a ha b hb
        exact safe a (List.mem_of_mem_drop ha) b (List.mem_of_mem_drop hb))
    obtain ⟨result, result_done, result_mem⟩ := mergeExecution_returns compare left right (by
      intro a ha b hb
      exact safe a (List.mem_of_mem_take (left_mem a ha))
        b (List.mem_of_mem_drop (right_mem b hb)))
    refine ⟨result, ?_, ?_⟩
    · rw [mergeSortExecution, dif_neg short]
      exact Execution.finishes_bind_ok left_done
        (Execution.finishes_bind_ok right_done result_done)
    · intro value member
      rcases result_mem value member with h | h
      · exact List.mem_of_mem_take (left_mem value h)
      · exact List.mem_of_mem_drop (right_mem value h)
termination_by values.length
decreasing_by
  all_goals
    simp_wf
    have positive : 0 < values.length := by omega
    have half_lt := Nat.div_lt_self positive (by decide : 1 < 2)
    have _half_positive : 0 < values.length / 2 := by omega
    omega

/-- Exact AST template for the supported merge-sort implementation. -/
def mergeSortBody (functionName argument : String) : List Stmt := [
  .ifThen (.compare (.builtinCall .len [.name argument]) [(.ltE, .constant (.int 1))])
    [.return (.name argument)] [],
  .assign [.name "middle"]
    (.binOp (.builtinCall .len [.name argument]) .floorDiv (.constant (.int 2))),
  .assign [.name "left"] (.call (.name functionName)
    [.subscript (.name argument) (.slice none (some (.name "middle")) none)]),
  .assign [.name "right"] (.call (.name functionName)
    [.subscript (.name argument) (.slice (some (.name "middle")) none none)]),
  .assign [.name "merged"] (.list []),
  .assign [.name "left_index"] (.constant (.int 0)),
  .assign [.name "right_index"] (.constant (.int 0)),
  .whileDo (.boolOp .and [
    .compare (.name "left_index") [(.lt, .builtinCall .len [.name "left"])],
    .compare (.name "right_index") [(.lt, .builtinCall .len [.name "right"])]] ) [
    .ifThen (.compare (.subscript (.name "left") (.name "left_index"))
      [(.ltE, .subscript (.name "right") (.name "right_index"))]) [
      .augAssign (.name "merged") .add (.list [.subscript (.name "left") (.name "left_index")]),
      .augAssign (.name "left_index") .add (.constant (.int 1))
    ] [
      .augAssign (.name "merged") .add (.list [.subscript (.name "right") (.name "right_index")]),
      .augAssign (.name "right_index") .add (.constant (.int 1))
    ]
  ] [],
  .return (.binOp
    (.binOp (.name "merged") .add
      (.subscript (.name "left") (.slice (some (.name "left_index")) none none)))
    .add (.subscript (.name "right") (.slice (some (.name "right_index")) none none)))
]

/-- Accept exactly the supported merge-sort AST. Adding a loop or changing an
operation makes this unsupported, rather than silently assuming termination. -/
def isMergeSortFunction (module : Module) (name : String) : Bool :=
  match findFunctionIn module.body name with
  | some ([argument], body) => executableBody body == mergeSortBody name argument.name
  | _ => false

def listFunction (module : Module) (name : String) (values : List Value) : Execution (List Value) :=
  if isMergeSortFunction module name then
    mergeSortExecution (comparison module .ltE) values
  else Execution.unsupported

end FormalSW.PyAst

namespace FormalSW.Property.Function

/-- At least one input ends by raising an exception. Bare lists and unary integers
use execution semantics; untyped binary comparison demos use the abstract model. -/
def Throws (module : PyAst.Module) (name : String) : Prop :=
  match module.findFunctionArgKind name with
  | some .int => ∃ n : Int, (PyAst.scalarFunction module name [.int n]).Throws
  | some .valueList => ∃ values : List PyAst.Value, (PyAst.listFunction module name values).Throws
  | _ => AbstractThrows module name

end FormalSW.Property.Function
