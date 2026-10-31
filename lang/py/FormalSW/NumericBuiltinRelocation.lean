import lang.py.FormalSW.MachineExceptionInvariant

/-! Scalar conversions and numeric protocol guards retain the modeled result and errors. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- Unknown numeric methods are not replaced with builtin TypeError results. -/
def numericProtocol (heap : Mutable.Heap) : Value → Bool
  | .scalar _ => false
  | .ref address => match heap[address]? with
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) | none => true
      | _ => false

theorem numericProtocol_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (value : Value) (inside : value.edge.Within logical.length) :
    numericProtocol physical (relocateValue rename value) = numericProtocol logical value := by
  cases value with
  | scalar scalar => rfl
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;> simp only [object, relocateObject] at moved <;>
      simp [numericProtocol, relocateValue, found, object, moved]

theorem numericProtocols_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (values : List Value)
    (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    (values.map (relocateValue rename)).any (numericProtocol physical) = values.any (numericProtocol logical) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [List.map_cons, List.any_cons, numericProtocol_relocates logical physical rename layout value (inside value (by simp)),
      ih (fun value member => inside value (by simp [member]))]

def powerResult (heap : Mutable.Heap) : List Value → Option (Except ExceptionObject Constant)
  | [.scalar base, .scalar exponent] => scalarBinary .pow base exponent
  | [base, exponent] => if [base, exponent].any (numericProtocol heap) then none else some (.error ⟨"TypeError", []⟩)
  | [.scalar base, .scalar exponent, .scalar modulus] => Calls.modularPower base exponent modulus
  | [base, exponent, modulus] => if [base, exponent, modulus].any (numericProtocol heap) then none else some (.error ⟨"TypeError", []⟩)
  | _ => some (.error ⟨"TypeError", []⟩)

theorem numericProtocolFailure_result (heap : Mutable.Heap) (unknown : Bool) :
    (if unknown then Mutable.unsupported else Mutable.error "TypeError" : Mutable.Eval Value) heap =
      scalarResult (if unknown then none else some (.error ⟨"TypeError", []⟩)) heap := by
  cases unknown <;> rfl

theorem primitive_power_result (heap : Mutable.Heap) (values : List Value) :
    primitive (.builtin .pow) values heap = scalarResult (powerResult heap values) heap := by
  rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals try rfl
  all_goals cases first <;> try cases second <;> try cases third
  all_goals first | rfl | exact numericProtocolFailure_result heap _

theorem powerResult_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (values : List Value)
    (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    powerResult physical (values.map (relocateValue rename)) = powerResult logical values := by
  have protocols := numericProtocols_relocates logical physical rename layout values inside
  rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals try rfl
  all_goals cases first <;> try cases second <;> try cases third
  all_goals try rfl
  all_goals simpa only [powerResult, List.map_cons, List.map_nil, relocateValue] using
    congrArg (fun (unknown : Bool) => (if unknown then none else some (.error ⟨"TypeError", []⟩) : Option (Except ExceptionObject Constant))) protocols

def scalarArgumentCall (convert : List Constant → Option (Except ExceptionObject Constant)) (values : List Value) : Mutable.Eval Value := do
  let scalars ← values.mapM fun value => match value with
    | .scalar scalar => pure scalar
    | .ref _ => Mutable.unsupported
  scalarResult (convert scalars)

theorem scalarArgumentCall_result (convert : List Constant → Option (Except ExceptionObject Constant))
    (values : List Value) (heap : Mutable.Heap) :
    scalarArgumentCall convert values heap = scalarResult ((exceptionArguments values).bind convert) heap := by
  rw [scalarArgumentCall, Mutable.eval_bind]
  erw [exceptionArguments_eval]
  cases exceptionArguments values <;> rfl

def integerReferenceResult : Option Mutable.Object → Option (Except ExceptionObject Constant)
  | some (.bytearray bytes) => Calls.integerConversion [.bytes bytes]
  | some _ => some (.error ⟨"TypeError", []⟩)
  | none => none

def ordinalReferenceResult : Option Mutable.Object → Option (Except ExceptionObject Constant)
  | some (.bytearray bytes) => some (Strings.ord (.bytes bytes))
  | some _ => some (.error ⟨"TypeError", []⟩)
  | none => none

theorem primitive_int_ref (heap : Mutable.Heap) (address : Nat) :
    primitive (.builtin .int) [.ref address] heap = scalarResult (integerReferenceResult heap[address]?) heap := by
  cases found : heap[address]? with
  | none => simp [primitive, found, integerReferenceResult, scalarResult, Mutable.unsupported]
  | some object => cases object <;> simp [primitive, found, integerReferenceResult, scalarResult, Mutable.error]

theorem primitive_ord_ref (heap : Mutable.Heap) (address : Nat) :
    primitive (.builtin .ord) [.ref address] heap = scalarResult (ordinalReferenceResult heap[address]?) heap := by
  cases found : heap[address]? with
  | none => simp [primitive, found, ordinalReferenceResult, scalarResult, Mutable.unsupported]
  | some object => cases object <;> simp [primitive, found, ordinalReferenceResult, scalarResult, Mutable.error]

theorem primitive_bin_ref (heap : Mutable.Heap) (address : Nat) :
    primitive (.builtin .bin) [.ref address] heap =
      scalarResult (if numericProtocol heap (.ref address) then none else some (.error ⟨"TypeError", []⟩)) heap := by
  cases found : heap[address]? with
  | none => simp [primitive, found, numericProtocol, scalarResult, Mutable.unsupported]
  | some object => cases object <;> simp [primitive, found, numericProtocol, scalarResult, Mutable.error, Mutable.unsupported]

inductive ScalarBuiltinOperation : Operation → Prop
  | power : ScalarBuiltinOperation (.builtin .pow)
  | absolute : ScalarBuiltinOperation (.builtin .abs)
  | integerType : ScalarBuiltinOperation (.builtin .isinstanceInt)
  | binaryText : ScalarBuiltinOperation (.builtin .bin)
  | ordinal : ScalarBuiltinOperation (.builtin .ord)
  | bitLength : ScalarBuiltinOperation (.builtin .intBitLength)
  | bitCount : ScalarBuiltinOperation (.builtin .intBitCount)
  | integer : ScalarBuiltinOperation (.builtin .int)
  | text : ScalarBuiltinOperation (.builtin .str)
  | representation : ScalarBuiltinOperation (.builtin .repr)

/-- A common scalar result includes modeled errors and unsupported cases. -/
theorem scalarBuiltin_pair (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (operation : Operation) (covered : ScalarBuiltinOperation operation)
    (values : List Value) (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    ∃ outcome : Option (Except ExceptionObject Constant),
      primitive operation values logical = scalarResult outcome logical ∧
      primitive (relocateOperation rename operation) (values.map (relocateValue rename)) physical = scalarResult outcome physical := by
  cases covered with
  | power =>
    exact ⟨powerResult logical values, primitive_power_result logical values, by
      simp only [relocateOperation, primitive_power_result, powerResult_relocates logical physical rename layout values inside]⟩
  | text =>
    refine ⟨(exceptionArguments values).bind (fun scalars => some (Strings.str scalars)), ?_, ?_⟩
    · exact scalarArgumentCall_result _ values logical
    · exact (scalarArgumentCall_result _ _ physical).trans (by rw [exceptionArguments_relocates])
  | integer =>
    rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
    case nil => exact ⟨Calls.integerConversion [], rfl, rfl⟩
    case cons.nil =>
      cases value with
      | scalar scalar => exact ⟨Calls.integerConversion [scalar], rfl, rfl⟩
      | ref address =>
        have addressInside : address < logical.length := inside (.ref address) (by simp)
        have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem addressInside
        have moved := layout.lookup address _ found
        refine ⟨integerReferenceResult logical[address]?, primitive_int_ref logical address, ?_⟩
        simp only [relocateOperation, List.map_cons, List.map_nil, relocateValue, primitive_int_ref]
        cases object : logical[address] <;> simp only [object, relocateObject] at moved <;>
          simp only [found, object, moved, integerReferenceResult]
    case cons.cons =>
      refine ⟨(exceptionArguments (value :: extra :: rest)).bind Calls.integerConversion, ?_, ?_⟩
      · cases value <;> exact scalarArgumentCall_result _ _ logical
      · have paired := scalarArgumentCall_result Calls.integerConversion ((value :: extra :: rest).map (relocateValue rename)) physical
        rw [exceptionArguments_relocates] at paired
        cases value <;> exact paired
  | binaryText =>
    rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
    case cons.nil =>
      cases value with
      | scalar scalar => exact ⟨some (Strings.bin [scalar]), rfl, rfl⟩
      | ref address =>
        refine ⟨_, primitive_bin_ref logical address, ?_⟩
        simp only [relocateOperation, List.map_cons, List.map_nil, relocateValue, primitive_bin_ref]
        have paired := numericProtocol_relocates logical physical rename layout (.ref address) (inside _ (by simp))
        simp only [relocateValue] at paired
        rw [paired]
    all_goals try exact ⟨some (.error ⟨"TypeError", []⟩), rfl, rfl⟩
    all_goals cases value <;> exact ⟨some (.error ⟨"TypeError", []⟩), rfl, rfl⟩
  | ordinal =>
    rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
    case cons.nil =>
      cases value with
      | scalar scalar => exact ⟨some (Strings.ord scalar), rfl, rfl⟩
      | ref address =>
        have addressInside : address < logical.length := inside (.ref address) (by simp)
        have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem addressInside
        have moved := layout.lookup address _ found
        refine ⟨ordinalReferenceResult logical[address]?, primitive_ord_ref logical address, ?_⟩
        simp only [relocateOperation, List.map_cons, List.map_nil, relocateValue, primitive_ord_ref]
        cases object : logical[address] <;> simp only [object, relocateObject] at moved <;>
          simp only [found, object, moved, ordinalReferenceResult]
    all_goals try exact ⟨none, rfl, rfl⟩
    all_goals cases value <;> exact ⟨none, rfl, rfl⟩
  | absolute =>
    rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
    case nil => exact ⟨some (.error ⟨"TypeError", []⟩), rfl, rfl⟩
    case cons.nil =>
      cases value with
      | scalar scalar => exact ⟨some (Calls.absoluteValue scalar), rfl, rfl⟩
      | ref address => exact ⟨some (.error ⟨"TypeError", []⟩), rfl, rfl⟩
    case cons.cons => cases value <;> exact ⟨some (.error ⟨"TypeError", []⟩), rfl, rfl⟩
  | integerType =>
    rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
    case nil => exact ⟨some (.error ⟨"TypeError", []⟩), rfl, rfl⟩
    case cons.nil =>
      cases value with
      | scalar scalar => exact ⟨some (.ok (.bool (Calls.isInteger scalar))), rfl, rfl⟩
      | ref address => exact ⟨some (.ok (.bool false)), rfl, rfl⟩
    case cons.cons => cases value <;> exact ⟨some (.error ⟨"TypeError", []⟩), rfl, rfl⟩
  | bitLength =>
    rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
    case nil => exact ⟨none, rfl, rfl⟩
    case cons.nil =>
      cases value with
      | scalar scalar => exact ⟨some (Math.bitLengthCall scalar), rfl, rfl⟩
      | ref address => exact ⟨some (.error ⟨"AttributeError", []⟩), rfl, rfl⟩
    case cons.cons => cases value <;> exact ⟨none, rfl, rfl⟩
  | bitCount =>
    rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
    case nil => exact ⟨none, rfl, rfl⟩
    case cons.nil =>
      cases value with
      | scalar scalar => exact ⟨some (Math.bitCountCall scalar), rfl, rfl⟩
      | ref address => exact ⟨some (.error ⟨"AttributeError", []⟩), rfl, rfl⟩
    case cons.cons => cases value <;> exact ⟨none, rfl, rfl⟩
  | representation =>
    rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
    case nil => exact ⟨some (.error ⟨"TypeError", []⟩), rfl, rfl⟩
    case cons.nil =>
      cases value with
      | scalar scalar => exact ⟨some (.ok (.string (Strings.reprValue scalar))), rfl, rfl⟩
      | ref address => exact ⟨none, rfl, rfl⟩
    case cons.cons => cases value <;> exact ⟨some (.error ⟨"TypeError", []⟩), rfl, rfl⟩

end FormalSW.PyAst.HeapCalls.Relocation
