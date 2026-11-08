import lang.py.FormalSW.HeapRuntimeCostSumGenerators
import lang.py.FormalSW.HeapRuntimeCostPrimitives
import lang.py.FormalSW.DecimalWorkBounds
import lang.py.FormalSW.IntegerParsing

namespace FormalSW.PyAst.HeapCalls.Runtime.DecimalSum
set_option maxHeartbeats 1000000

def expression (input : Expr) : Expr :=
  .sumGenerator (.builtinCall .int [.name "ch"])
    [("ch", .builtinCall .str [input], [])] (.constant (.int 0))

private theorem parse_digit (c : Char) (digit : c.isDigit) :
    Calls.integerConversion [.string (String.singleton c)] =
      some (.ok (.int ((c.toNat - '0'.toNat : Nat) : Int))) := by
  change Calls.integerConversion [.string (String.ofList [c])] = _
  rw [Calls.integerConversion, FormalSW.Py.Builtin.Int.parseText_digits [c] (by simp)
    (by intro d member; simp only [List.mem_singleton] at member; subst d; exact digit)]
  simp [Calls.parsedInteger, Nat.ofDigitChars]

/-- Decimal conversion is followed by one parsed character and one addition per digit. -/
theorem evaluates (n k : Nat) (positive : 0 < k) (bounded : n < 10^k)
    (input : EvaluatesIn .word module env source heap cost (.scalar (.int n)) heap) :
    ∃ answer, EvaluatesIn .word module env (expression source) heap
      (cost+24*k+25) (.scalar (.int answer)) heap := by
  let characters := (toString n).toList
  let value := fun c : {c // c ∈ characters} => ((c.val.toNat - '0'.toNat : Nat) : Int)
  have converted : EvaluatesIn .word module env (.builtinCall .str [source]) heap
      (cost+PrimitiveWork.bitLength (n : Int)+4) (.scalar (.string (toString n))) heap := by
    have run := EvaluatesIn.builtin_single (builtin := .str)
      (work := PrimitiveWork.bitLength (n : Int)+1) (by intro h; cases h) (by intro h; cases h) input (by rfl) rfl
    exact run.mono (by omega)
  have digits : ∀ env c, env "ch" = some (.scalar (.string (String.singleton c.val))) →
      EvaluatesIn .word module env (.builtinCall .int [.name "ch"]) heap 8
        (.scalar (.int (value c))) heap := by
    intro env c get
    apply EvaluatesIn.builtin_single (builtin := .int) (work := 4) (ca := 1)
      (value := .scalar (.string (String.singleton c.val)))
      (answer := .scalar (.int (value c))) (by intro h; cases h) (by intro h; cases h)
      (EvaluatesIn.lookup get)
    · change scalarResult (Calls.integerConversion [.string (String.singleton c.val)]) heap = _
      have member : c.val ∈ Nat.toDigits 10 n := by simpa [characters] using c.property
      rw [parse_digit c.val (Nat.isDigit_of_mem_toDigits (by decide) (by decide) member)]
      rfl
    · simp [operation, scalarValues, Calls.Runtime.primitive, String.length_singleton]
  let sumEnv := setLocal (comprehensionEnv env [("ch", .builtinCall .str [source], [])])
    sumAccumulator (.scalar (.int 0))
  have loop := sum_sequence_loop (module := module) (env := sumEnv) (initial := 0)
    (source := .scalar (.string (toString n))) (name := "ch")
    (values := characters.attach) (encode := fun c => .scalar (.string (String.singleton c.val)))
    (number := value) characters.attach 0 8 (by decide)
    (by simp [Mutable.sequence, sequenceValue, characters])
    (by intro name position body otherwise following env stack; rfl) digits rfl (by simp [sumEnv, setLocal])
  have run := EvaluatesIn.sum_generator
    (items := characters.map (fun c => .scalar (.string (String.singleton c))))
    (by intro expressions impossible; cases impossible) converted
    (by simp [Mutable.sequence, characters]) (by rfl) EvaluatesIn.constant loop
  refine ⟨characters.attach.foldl (fun total c => total+value c) 0, ?_⟩
  have width := PrimitiveWork.bitLength_decimal n k bounded
  have length := PrimitiveWork.decimal_length n k positive bounded
  have length' : characters.length ≤ k := by
    change (toString n).toList.length ≤ k
    rw [String.length_toList]
    simpa [Int.repr_eq_if] using length
  apply run.mono
  simp only [List.length_attach]
  omega

end FormalSW.PyAst.HeapCalls.Runtime.DecimalSum
