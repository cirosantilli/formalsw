import «.formalsw».tests.py.«string_digits.py.ast»
import FormalSW

namespace tests.py.string_digits
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := StringDigitsAst.module
private def encode (character : Char) : Mutable.Value :=
  .scalar (.string (String.ofList [character]))
private def digit (character : Char) : Bool := FormalSW.Py.Builtin.Unicode.isDigit character.toNat
private def scanBody : List Stmt :=
  [.ifThen (.unaryOp .not (.call (.attribute (.name "character") "isdigit") []))
    [.return (.constant (.bool false))] []]

private theorem scan (text : String) (remaining : List Char) (position : Nat)
    (suffix : text.toList.drop position = remaining) (heap : Heap) (env : Mutable.Env) :
    BlockReturns program env
      [.sequenceStepLoop "character" (.scalar (.string text)) position scanBody [],
        .return (.constant (.bool true))]
      heap (.scalar (.bool (remaining.all digit))) heap := by
  have sequence : Mutable.sequence (.scalar (.string text)) heap =
      some (.ok (text.toList.map encode), heap) := rfl
  induction remaining generalizing position env with
  | nil =>
      apply BlockReturns.sequence_done (source := .scalar (.string text)) sequence
      · have missing : text.toList[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := text.toList) (i := position)).symm
        simp [missing]
      · exact BlockReturns.return_value Evaluates.constant
  | cons head tail ih =>
      have item : text.toList[position]? = some head := by
        simpa [suffix] using (List.head?_drop (l := text.toList) (i := position)).symm
      apply BlockReturns.sequence_step (source := .scalar (.string text))
        (value := encode head) sequence (by simp [item])
      have evaluated := Evaluates.is_digit (globals := []) (module := program) (heap := heap)
        (base := .name "character") (text := String.ofList [head])
        (env := setLocal env "character" (encode head)) (Evaluates.lookup rfl)
        (by intro name equal; cases equal; rfl)
      have single : Strings.isDigit (String.ofList [head]) = digit head := by
        simp [Strings.isDigit, digit]
      rw [single] at evaluated
      cases accepted : digit head with
      | false =>
          simp only [List.all_cons, accepted, Bool.false_and]
          apply BlockReturns.branch (flag := true)
            (Evaluates.unary (by simpa [accepted] using evaluated) rfl) rfl
          exact BlockReturns.return_value Evaluates.constant
      | true =>
          simp only [List.all_cons, accepted, Bool.true_and]
          apply BlockReturns.branch (flag := false)
            (Evaluates.unary (by simpa [accepted] using evaluated) rfl) rfl
          have rest := ih (position + 1)
            (by simp [List.drop_add_one_eq_tail_drop, suffix])
            (setLocal env "character" (encode head))
          simpa [scanBody, Calls.loopContinuation, Calls.loopControl,
            Calls.loopControlStmt] using rest

theorem reference.result (text : String) (heap : Heap) :
    ReturnsValue program "reference" [.scalar (.string text)] heap
      (.scalar (.bool (Strings.isDigit text))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (flag := text.isEmpty) (value := .scalar (.bool text.isEmpty))
    (middle := heap)
    (Evaluates.unary (Evaluates.lookup rfl)
      (by simp [HeapCalls.unary, Mutable.truth, scalarTruth])) rfl
  cases empty : text.isEmpty with
  | true =>
      simp only [if_true, List.cons_append, List.nil_append]
      simpa [Strings.isDigit, empty] using
        (BlockReturns.return_value (module := program) (heap := heap) Evaluates.constant)
  | false =>
      simp only [Bool.false_eq_true, if_false, List.nil_append]
      apply BlockReturns.for_sequence (items := text.toList.map encode)
        (by intro arguments impossible; cases impossible) (Evaluates.lookup rfl) rfl
      simpa [Strings.isDigit, empty, digit] using scan text text.toList 0 rfl heap _

theorem solve.result (text : String) (heap : Heap) :
    ReturnsValue program "solve" [.scalar (.string text)] heap
      (.scalar (.bool (Strings.isDigit text))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.is_digit (Evaluates.lookup rfl) (by intro name equal; cases equal; rfl)

theorem equivalent_heap (text : String) (heap : Heap) :
    (HeapCalls.call program "solve" [.scalar (.string text)] heap).Equiv
      (HeapCalls.call program "reference" [.scalar (.string text)] heap) :=
  Mutable.Call.equiv_of_finishes (solve.result text heap).finishes
    (reference.result text heap).finishes (.inl rfl)

theorem reference.«Returns» (text : String) :
    (HeapCalls.scalarFunction program "reference" [.string text]).Returns :=
  (reference.result text []).scalar_returns

theorem reference.«Supported» (text : String) :
    (HeapCalls.scalarFunction program "reference" [.string text]).Supported :=
  (reference.«Returns» text).supported

theorem solve.«Returns» (text : String) :
    (HeapCalls.scalarFunction program "solve" [.string text]).Returns :=
  (solve.result text []).scalar_returns

theorem solve.«Equiv(reference)» (text : String) :
    (HeapCalls.scalarFunction program "solve" [.string text]).Equiv
      (HeapCalls.scalarFunction program "reference" [.string text]) := by
  intro outcome
  constructor
  · intro run
    rw [run.unique (solve.result text []).scalar_finishes]
    exact (reference.result text []).scalar_finishes
  · intro run
    rw [run.unique (reference.result text []).scalar_finishes]
    exact (solve.result text []).scalar_finishes

theorem solve.«Supported» :
    (∀ text : String, (HeapCalls.scalarFunction program "solve" [.string text]).Supported) ∧
      (∀ text : String, (HeapCalls.scalarFunction program "reference" [.string text]).Supported) :=
  ⟨fun text => (solve.«Returns» text).supported, reference.«Supported»⟩

end tests.py.string_digits
