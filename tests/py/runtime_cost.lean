import lang.py.FormalSW.CallsRuntimeCost
import lang.py.FormalSW.HeapMapWork
import lang.py.FormalSW.PrimitiveWorkBounds
import lang.py.FormalSW.CallsRuntimeCostScaled
import lang.py.FormalSW.CallsRuntimeCostStrings
import lang.py.FormalSW.HeapRuntimeCostControl
import lang.py.FormalSW.HeapRuntimeCostBuffers
import lang.py.FormalSW.HeapRuntimeCostBufferLoops
import lang.py.FormalSW.HeapRuntimeCostSequences
import lang.py.FormalSW.HeapRuntimeCostListLoops
import lang.py.FormalSW.HeapRuntimeCostSets
import lang.py.FormalSW.HeapRuntimeCostComparisons
import lang.py.FormalSW.HeapRuntimeCostSorting
import lang.py.FormalSW.HeapRuntimeCostBooleans

open FormalSW.PyAst

private def emptyModule : Module := { body := [] }
private def gcdModule : Module := { body := [.importFrom "math" [("gcd", "gcd")]] }
private def sqrtModule : Module := { body := [.importFrom "math" [("isqrt", "isqrt")]] }
private def combModule : Module := { body := [.importFrom "math" [("comb", "choose")]] }
private def factorialModule : Module := { body := [.importFrom "math" [("factorial", "fact")]] }

/-- Factorial follows all factors, including the empty product, and checks signs
before looping. The bit model charges the growing intermediate products. -/
example : Calls.Runtime.library .word factorialModule "fact" [.int 10] = some 88 := rfl
example : Calls.Runtime.library .word factorialModule "fact" [.int 0] = some 8 := rfl
example : Calls.Runtime.library .word factorialModule "fact" [.int (-1)] = some 2 := rfl
example : Calls.Runtime.library .bits factorialModule "fact" [.int 4] = some 17640 := rfl
example : Calls.Runtime.library .bits factorialModule "fact" [.int (-(2^100))] = some 102 := rfl
example : Calls.Runtime.library .word factorialModule "factorial" [.int 4] = none := rfl
example : Calls.Runtime.library .word factorialModule "fact" [.string "4"] = none := rfl

/-- Library work follows the smaller number of factors, including aliases,
empty products and error exits. Bit costs also account for intermediate widths. -/
example : Calls.Runtime.library .word combModule "choose" [.int 40, .int 20] = some 168 := rfl
example : Calls.Runtime.library .word combModule "choose" [.int 40, .int 39] = some 16 := rfl
example : Calls.Runtime.library .word combModule "choose" [.int 40, .int 0] = some 8 := rfl
example : Calls.Runtime.library .word combModule "choose" [.int 40, .int 41] = some 1 := rfl
example : Calls.Runtime.library .word combModule "choose" [.int (-1), .int 0] = some 1 := rfl
example : Calls.Runtime.library .bits combModule "choose" [.int 4, .int 2] = some 10584 := rfl
example : Calls.Runtime.library .bits combModule "choose" [.int 4, .int (2^100)] = some 417 := rfl
example : Calls.Runtime.library .word combModule "comb" [.int 4, .int 2] = none := rfl
example : Calls.Runtime.library .word combModule "choose" [.string "4", .int 2] = none := rfl

/-- Sorting pays for comparison work and copying; it is constant here only
because the input arity is three and integer arithmetic is fixed-cost. -/
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation (.builtin .sorted) [.ref 0], [], [.tuple [.scalar (.int 3), .scalar (.int 1), .scalar (.int 2)]]⟩ =
    some 41 := by decide
example : HeapCalls.Runtime.charge .bits emptyModule
    ⟨.operation (.builtin .sorted) [.ref 0], [], [.list [.scalar (.int (2^100)), .scalar (.int 1), .scalar (.int 2)]]⟩ =
    some 2441 := by decide
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation (.builtin .sorted) [.ref 0], [], [.list (List.replicate 16 (.scalar (.int 1))) ]⟩ =
    some 273 := by decide
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation (.builtin .sorted) [.ref 0], [], [.list [.ref 1], .list []]⟩ = none := rfl
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.block [.assign [.tuple [.name "a", .name "b", .name "c"]] (.name "xs")] (fun _ => none), [], []⟩ =
    some 4 := rfl
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.value (.ref 0), [.unpack ["a", "b", "c"] [] (fun _ => none)], [.list [.ref 1, .ref 1, .ref 1]]⟩ =
    some 7 := rfl

/-- Sets charge worst-case search plus rebuilding, even for existing keys.
An extremum scans all stored elements; arbitrary object protocols stay unpriced. -/
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation (.add 0) [.scalar (.int 2)], [], [.set [.int 1, .int 2, .int 3]]⟩ = some 37 := by decide
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation (.builtin .max) [.ref 0], [], [.set [.int 1, .int 2, .int 3]]⟩ = some 13 := by decide
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation (.add 0) [.ref 1], [], [.set [], .list []]⟩ = none := rfl
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation (.add 0) [.scalar (.int 1)], [], [.list []]⟩ = none := rfl
example : HeapCalls.SetWork.insert .collisionChain .word [.int (2^100)] (.int 1) = 18 := by decide
example : HeapCalls.SetWork.insert .collisionChain .bits [.int (2^100)] (.int 1) = 618 := by decide
example : HeapCalls.SetWork.insert .collisionChain .word [.string "long key"] (.int 1) = 66 := by decide
example : HeapCalls.Runtime.EvaluatesIn .word emptyModule (fun _ => some (.ref 0))
    (.call (.attribute (.name "out") "add") [.constant (.int 3)]) [.set [.int 1, .int 2]]
    33 (.scalar .none) [.set [.int 1, .int 2, .int 3]] :=
  HeapCalls.Runtime.EvaluatesIn.set_add (arithmetic := .word) (address := 0)
    (old := [.int 1, .int 2]) (current := [.int 1, .int 2]) (value := .int 3)
    (HeapCalls.Runtime.EvaluatesIn.lookup rfl) rfl
    HeapCalls.Runtime.EvaluatesIn.constant rfl
example : HeapCalls.Runtime.EvaluatesIn .word emptyModule (fun _ => some (.ref 0))
    (.builtinCall .max [.name "out"]) [.set [.int 3, .int 1, .int 2]]
    16 (.scalar (.int 3)) [.set [.int 3, .int 1, .int 2]] :=
  HeapCalls.Runtime.EvaluatesIn.set_maximum (arithmetic := .word) (address := 0)
    (items := [.int 3, .int 1, .int 2]) (answer := .int 3)
    (HeapCalls.Runtime.EvaluatesIn.lookup rfl) rfl (by decide)

/-- Fresh slices charge selected references, including Python's negative-stop
normalization; invalid strides have no successful-copy tariff. -/
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation .slice [.ref 0, .scalar .none, .scalar (.int (-2)), .scalar .none], [],
      [.list (List.replicate 10 (.scalar (.int 7))) ]⟩ = some 250 := by decide
example : HeapCalls.SequenceWork.slice .word 10 (.scalar .none) (.scalar (.int (-20))) (.scalar .none) =
    some 201 := by decide
example : HeapCalls.SequenceWork.slice .word 10 (.scalar .none) (.scalar .none) (.scalar (.int 0)) =
    none := by decide
example : HeapCalls.SequenceWork.slice .word 10 (.scalar .none) (.scalar (.string "bad")) (.scalar .none) =
    none := rfl

/-- Concatenation copies both lists; in-place growth has its own resizing tariff. -/
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.value (.ref 1), [.binaryRight .add (.ref 0) false],
      [.list (List.replicate 2 (.scalar (.int 7))), .list (List.replicate 3 (.ref 0))]⟩ = some 9 := by decide
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.value (.ref 1), [.binaryRight .add (.ref 0) true], [.list [], .list []]⟩ = some 2 := rfl

/-- A list iterator pays for each bounds check, pointer read and cursor update;
bit arithmetic also charges cursor width. Setup does not copy the list. -/
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.block [.sequenceStepLoop "x" (.ref 0) (2^100) [] []] (fun _ => none), [], [.list []]⟩ = some 5 := rfl
example : HeapCalls.Runtime.charge .bits emptyModule
    ⟨.block [.sequenceStepLoop "x" (.ref 0) (2^100) [] []] (fun _ => none), [], [.list []]⟩ = some 205 := by decide
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.value (.ref 0), [.sequence "x" [] [] [] (fun _ => none)], [.list (List.replicate 100 (.scalar .none))]⟩ =
    some 1 := rfl

/-- Indexed reads charge bounds/address arithmetic without traversing the list.
The element is a pointer-sized copy, even when it refers to another container. -/
example (items : List Mutable.Value) : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation .subscript [.ref 0, .scalar (.int (-1))], [], [.list items]⟩ = some 4 := rfl
example : HeapCalls.Runtime.charge .bits emptyModule
    ⟨.operation .subscript [.ref 0, .scalar (.int 1)], [], [.list [.ref 1, .ref 1], .list []]⟩ = some 5 := by decide
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation .subscript [.ref 0, .scalar (.string "bad")], [], [.list []]⟩ = none := rfl
example : HeapCalls.Runtime.EvaluatesIn .word emptyModule (fun name =>
    if name = "xs" then some (.ref 0) else none) (.subscript (.name "xs") (.constant (.int (-1))))
    [.list [.scalar (.int 4), .ref 1], .list []] 10 (.ref 1) [.list [.scalar (.int 4), .ref 1], .list []] :=
  HeapCalls.Runtime.EvaluatesIn.list_subscript (by intros; simp)
    (HeapCalls.Runtime.EvaluatesIn.lookup rfl) HeapCalls.Runtime.EvaluatesIn.constant rfl (by decide)

/-- Bit length follows the selected integer policy; a successful assertion
charges its control step after the separately measured condition. -/
example : Calls.Runtime.primitive .word (.builtin .intBitLength) [.int (2^100)] = some 1 := rfl
example : Calls.Runtime.primitive .bits (.builtin .intBitLength) [.int (2^100)] = some 101 := by decide
example : Calls.Runtime.primitive .word (.builtin .intBitLength) [.string "123"] = none := rfl
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.block [.assert (.constant (.bool true)) none] (fun _ => none), [], []⟩ = some 1 := rfl
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.value (.scalar (.bool true)), [.assertion none [] (fun _ => none)], []⟩ = some 1 := rfl

/-- Buffer enumeration accounts for counter/index widths under bit arithmetic.
The iterator is not a materialized copy of the semantic sequence. -/
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.block [.enumerateStepLoop "i" "x" (.ref 0) (2^100) (2^100) [] []] (fun _ => none), [],
      [.bytearray [1,2,3]]⟩ = some 7 := by decide
example : HeapCalls.Runtime.charge .bits emptyModule
    ⟨.block [.enumerateStepLoop "i" "x" (.ref 0) (2^100) (2^100) [] []] (fun _ => none), [],
      [.bytearray [1,2,3]]⟩ = some 308 := by decide

/-- Buffer iteration rules do not silently supply a tariff for other containers. -/
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.block [.enumerateStepLoop "i" "x" (.ref 0) 0 0 [] []] (fun _ => none), [],
      [.list []]⟩ = none := rfl

/-- Fixed arithmetic still charges byte allocation and repetition by output size. -/
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation (.builtin .bytearray) [.scalar (.bytes (List.replicate 8 1))], [], []⟩ = some 10 := by decide
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.value (.scalar (.int 3)), [.binaryRight .mult (.ref 0) false],
      [.bytearray (List.replicate 8 1)]⟩ = some 27 := by decide

/-- Successful extended replacement pays per written byte, not for unrelated bytes. -/
example (bytes : List UInt8) : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation (.setSlice (.scalar (.bytes (List.replicate 4 0))))
      [.ref 0, .scalar (.int 0), .scalar .none, .scalar (.int 2)], [], [.bytearray bytes]⟩ = some 226 := by
  simp [HeapCalls.Runtime.charge, HeapCalls.Runtime.operation, HeapCalls.BufferWork.operation,
    HeapCalls.BufferWork.slice, HeapCalls.BufferWork.sliceWidth, HeapCalls.BufferWork.bound,
    PrimitiveWork.integer, scalarNumber]

/-- Empty replacement deletes positions even with a stride; shifting is charged. -/
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation (.setSlice (.scalar (.bytes [])))
      [.ref 0, .scalar (.int 0), .scalar .none, .scalar (.int 2)], [],
      [.bytearray [1,2,3,4,5,6,7,8]]⟩ = some 246 := by decide
example : HeapCalls.Runtime.Reaches .word emptyModule 1
    ⟨.operation (.setSlice (.scalar (.bytes [])))
      [.ref 0, .scalar (.int 0), .scalar .none, .scalar (.int 2)], [],
      [.bytearray [1,2,3,4,5,6,7,8]]⟩ 246
    ⟨.value (.scalar .none), [], [.bytearray [2,4,6,8]]⟩ :=
  HeapCalls.Runtime.buffer_slice_operation _ _ _ _ _ _ _ _ rfl (by decide) (by decide)

/-- Contiguous replacement also pays for moving the suffix. -/
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation (.setSlice (.scalar (.bytes (List.replicate 4 0))))
      [.ref 0, .scalar (.int 0), .scalar (.int 2), .scalar .none], [],
      [.bytearray (List.replicate 8 1)]⟩ = some 266 := by decide

/-- List slice mutation still requires a capacity model; byte prices do not apply. -/
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation (.setSlice (.scalar (.bytes [])))
      [.ref 0, .scalar (.int 0), .scalar .none, .scalar (.int 2)], [], [.list []]⟩ = none := rfl

/-- A full array pays for copying; the next append fits in its spare capacity. -/
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation (.append 0) [.scalar (.int 0)], [], [.list (List.replicate 8 (.scalar (.int 0))) ]⟩ =
      some 10 := by decide
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.operation (.append 0) [.scalar (.int 0)], [], [.list (List.replicate 9 (.scalar (.int 0))) ]⟩ =
      some 2 := by decide
example : HeapCalls.Runtime.charge .bits emptyModule
    ⟨.operation (.append 0) [.scalar (.int (2^100))], [], [.list (List.replicate 8 (.scalar (.int 0))) ]⟩ =
      some 10 := by decide

/-- Arbitrarily many appends have a linear total even though individual resizes do not. -/
example (count : Nat) : PrimitiveWork.DynamicArray.appendMany 0 count ≤ 3 * count :=
  PrimitiveWork.DynamicArray.appendMany_empty count

/-- The amortized rule is attached to the actual Python append expression. -/
example (items : List HeapCalls.Value) : HeapCalls.Runtime.EvaluatesIn .word emptyModule
    (fun _ => some (.ref 0)) (.call (.attribute (.name "xs") "append") [.constant (.int 0)])
    [.list items] 9 (.scalar .none) [.list (items ++ [.scalar (.int 0)])] :=
  HeapCalls.Runtime.EvaluatesIn.append (address := 0) (old := items) (current := items)
    (middle := [.list items]) (afterItem := [.list items]) (HeapCalls.Runtime.EvaluatesIn.lookup rfl) rfl
    HeapCalls.Runtime.EvaluatesIn.constant rfl

/-- Shallow reversal copies pointers and reserves credits for its fresh array. -/
example (items : List HeapCalls.Value) : HeapCalls.Runtime.EvaluatesIn .word emptyModule
    (fun _ => some (.ref 0)) (.reversedList (.name "xs")) [.list items]
    (1 + 2 * items.length + 4) (.ref 1) [.list items, .list items.reverse] :=
  HeapCalls.Runtime.EvaluatesIn.reversed (HeapCalls.Runtime.EvaluatesIn.lookup rfl) rfl

/-- Shrinking an array needs its own capacity policy; ordinary termination is insufficient. -/
private def arrayPop : HeapCalls.State := ⟨.operation (.pop 0) [], [], [.list [.scalar (.int 7)]]⟩
example : HeapCalls.step emptyModule 1 arrayPop =
    .next ⟨.value (.scalar (.int 7)), [], [.list []]⟩ := rfl
example : HeapCalls.Runtime.charge .word emptyModule arrayPop = none := rfl
example : ¬ RuntimeCost.Finishes (HeapCalls.step emptyModule 1)
    (HeapCalls.Runtime.charge .word emptyModule) arrayPop cost outcome :=
  RuntimeCost.Finishes.impossible_of_missing rfl

/-- Nested comparisons cannot borrow the tariff for flat scalar lists. -/
example : HeapCalls.Runtime.charge .word emptyModule
    ⟨.value (.ref 1), [.compareRight .eq (.ref 0)],
      [.list [.ref 2], .list [.ref 3], .list [], .list []]⟩ = none := rfl

/-- Heap execution uses the same operand-sensitive arithmetic as scalar execution. -/
example : HeapCalls.Runtime.charge .bits emptyModule
    ⟨.value (.scalar (.int (2^100))), [.binaryRight .mult (.scalar (.int (2^100))) false], []⟩ =
      some 10202 := by decide

/-- Fixed arithmetic still pays for producing the decimal characters. -/
example : Calls.Runtime.charge .word emptyModule
    ⟨.primitive (.builtin .str) [.int (2^100)], []⟩ = some 103 := by decide
example : Calls.Runtime.charge .bits emptyModule
    ⟨.primitive (.builtin .str) [.int (2^100)], []⟩ = some 10203 := by decide

/-- Reversal pays for every character, as well as evaluating the slice arguments. -/
example (text : String) : RuntimeCost.Finishes (Calls.step emptyModule)
    (Calls.Runtime.charge .word emptyModule)
    ⟨.expr (Calls.Runtime.reverseString "s") (fun _ => some (.string text)), []⟩
    (text.length+28) (.ok (.string (String.ofList text.toList.reverse))) := by
  have run := Calls.Runtime.EvaluatesIn.reverse_string
    (module := emptyModule) (env := fun _ => some (.string text)) (name := "s") rfl []
  simpa only [Nat.add_assoc] using run.finishes (RuntimeCost.Finishes.done rfl rfl)

/-- Library work is charged even when the source has only one call expression. -/
example : Calls.Runtime.charge .bits sqrtModule
    ⟨.invoke "isqrt" [.int (2^100)], []⟩ = some 1030302 := by decide
example : Calls.Runtime.charge .word sqrtModule
    ⟨.invoke "isqrt" [.int (2^100)], []⟩ = some 102 := by decide

example : Calls.Runtime.Scaled.EvaluatesIn .bits sqrtModule 1 (fun _ => none)
    (.call (.name "isqrt") [.constant (.int 16)]) 129 (.int (Math.isqrt 16)) := by
  exact Calls.Runtime.Scaled.EvaluatesIn.library_single (by decide)
    (Calls.Runtime.Scaled.EvaluatesIn.constant (by decide)) rfl rfl
    (invokeBudget := 126) ⟨125, rfl, by decide⟩

/-- Scaling a source-step budget requires the real multiplication charge. -/
example : Calls.Runtime.Scaled.EvaluatesIn .bits emptyModule 10202 (fun _ => none)
    (.binOp (.constant (.int (2^100))) .mult (.constant (.int (2^100))))
    5 (.int ((2^100)*(2^100))) := by
  exact Calls.Runtime.Scaled.EvaluatesIn.binary (by decide)
    (Calls.Runtime.Scaled.EvaluatesIn.constant (by decide))
    (Calls.Runtime.Scaled.EvaluatesIn.constant (by decide)) rfl ⟨10201, by decide, by decide⟩

/-- A unit scaling factor cannot hide bit work in that same five-step expression. -/
example : ¬ Calls.Runtime.Scaled.EvaluatesIn .bits emptyModule 1 (fun _ => none)
    (.binOp (.constant (.int (2^100))) .mult (.constant (.int (2^100))))
    5 (.int ((2^100)*(2^100))) := by
  rintro ⟨cost, bound, run⟩
  have exactRun := Calls.Runtime.EvaluatesIn.binary
    (arithmetic := .bits) (module := emptyModule) (env := fun _ => none)
    (a := .constant (.int (2^100))) (b := .constant (.int (2^100))) (op := .mult)
    Calls.Runtime.EvaluatesIn.constant Calls.Runtime.EvaluatesIn.constant rfl
    (show PrimitiveWork.binary .bits .mult (.int (2^100)) (.int (2^100)) = some 10201 by decide)
  have same := ((run []).finishes (.done rfl rfl)).unique
    ((exactRun []).finishes (.done rfl rfl))
  omega

/-- Fixed arithmetic retains library work, controlled by the smaller gcd operand. -/
example : Calls.Runtime.charge .word gcdModule
    ⟨.invoke "gcd" [.int (2^100), .int (2^100)], []⟩ = some 103 := by decide
example : Calls.Runtime.charge .word gcdModule
    ⟨.invoke "gcd" [.int (2^100), .int 1], []⟩ = some 3 := by decide

/-- Even an empty range evaluates a guard, whose bit cost depends on the endpoints. -/
example : Calls.Runtime.charge .bits emptyModule
    ⟨.block [.rangeStepLoop "i" (2^100) (2^100) 1 [] []] (fun _ => none), []⟩ = some 204 := by decide
example : Calls.Runtime.charge .word emptyModule
    ⟨.block [.rangeStepLoop "i" (2^100) (2^100) 1 [] []] (fun _ => none), []⟩ = some 4 := rfl

/-- This primitive really executes, but has no runtime cost rule yet. -/
private def bitCount : Calls.State := ⟨.primitive (.builtin .intBitCount) [.int 7], []⟩
example : Calls.step emptyModule bitCount = .next ⟨.value (.int 3), []⟩ := rfl
example : Calls.Runtime.charge .bits emptyModule bitCount = none := rfl
example : ¬ RuntimeCost.Finishes (Calls.step emptyModule)
    (Calls.Runtime.charge .bits emptyModule) bitCount cost outcome :=
  RuntimeCost.Finishes.impossible_of_missing rfl

/-- Large operands are expensive even when multiplication uses one semantic step. -/
example : Calls.Runtime.charge .bits emptyModule
    ⟨.value (.int (2^100)), [.binaryRight .mult (.int (2^100))]⟩ = some 10202 := by decide
example : Calls.Runtime.charge .bits emptyModule
    ⟨.value (.int 2), [.binaryRight .mult (.int 2)]⟩ = some 5 := by decide

/-- Division by a fixed small integer grows linearly, not quadratically, in the dividend width. -/
example : Calls.Runtime.charge .bits emptyModule
    ⟨.value (.int 2), [.binaryRight .floorDiv (.int (2^100))]⟩ = some 203 := by decide

/-- Fixed arithmetic changes numeric primitives, not collection or copying costs. -/
example : Calls.Runtime.charge .word emptyModule
    ⟨.value (.int (2^100)), [.binaryRight .mult (.int (2^100))]⟩ = some 2 := rfl
example (text : String) : Calls.Runtime.charge .word emptyModule
    ⟨.value (.string text), [.binaryRight .add (.string text)]⟩ =
      some (text.length + text.length + 2) := rfl

/-- Copying a growing string cannot use a constant primitive charge. -/
example (text : String) : Calls.Runtime.charge .bits emptyModule
    ⟨.value (.string text), [.binaryRight .add (.string text)]⟩ =
      some (text.length + text.length + 2) := rfl

/-- The map rule is attached to the actual subscript operation and its heap receiver. -/
example (entries : List (Constant × Mutable.Value)) (key : Constant) :
    HeapCalls.MapWork.operation .balancedTree .bits [.dict entries] .subscript [.ref 0, .scalar key] =
      some (PrimitiveWork.mapLookup .balancedTree entries.length
        (HeapCalls.MapWork.keyWork .bits entries key)) :=
  HeapCalls.MapWork.subscript _ _ _ _ _ _ rfl

example : ¬ Growth.IsBigO (fun n => PrimitiveWork.mapLookup .balancedTree n 1) (fun _ => 1) :=
  PrimitiveWork.balancedLookup_not_constant 1

/-- Missing costs remain missing even when the original trace terminates immediately. -/
example : ¬ RuntimeCost.TimeBound (Execution.pure (7 : Nat)) (fun _ => none) bound := by
  rintro ⟨cost, outcome, run, _⟩
  exact RuntimeCost.Finishes.impossible_of_missing rfl run

private def forever : Execution Nat := ⟨Unit, (), fun _ => .next ()⟩

/-- Costs do not turn a divergent trace into a terminating one. -/
example : ¬ RuntimeCost.TimeBound forever (fun _ => some 1) bound := by
  intro bounded
  exact Execution.diverges_not_halts (execution := forever)
    (by exact ⟨fun _ => True, trivial, fun state _ => ⟨state, rfl, trivial⟩⟩) bounded.halts
