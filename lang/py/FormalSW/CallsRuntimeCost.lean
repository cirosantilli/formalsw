import lang.py.FormalSW.Calls
import lang.py.FormalSW.RuntimeCost
import lang.py.FormalSW.PrimitiveWork

/-! Operation-sensitive costs for the scalar call interpreter. Local variables,
control frames and resolved function identities are abstract machine operations;
integer/string primitives are charged from their operands. Unmodeled primitives
and library functions return `none`, which RuntimeCost refuses to prove through.
This is an algorithmic model, not the runtime of Lean's semantic data structures. -/
namespace FormalSW.PyAst.Calls.Runtime
open PrimitiveWork

def integerWork (arithmetic : Arithmetic) (value : Constant) : Option Nat :=
  (scalarNumber value).map (integer arithmetic)

def rangeWork (arithmetic : Arithmetic) (next stop stride : Int) : Nat :=
  1 + integer arithmetic next + integer arithmetic stop + integer arithmetic stride

def argumentWork (arithmetic : Arithmetic) (values : List Constant) : Nat :=
  1 + (values.map (scalarSize arithmetic)).sum

def library (arithmetic : Arithmetic) (module : Module) (name : String)
    (values : List Constant) : Option Nat :=
  match importedFunction module.body name, values with
  | some ("math", "gcd"), [left, right] => do
      let left ← scalarNumber left
      let right ← scalarNumber right
      let leftWidth := bitLength left
      let rightWidth := bitLength right
      let small := min leftWidth rightWidth
      -- The first remainder reduces a long operand to the smaller width;
      -- subsequent Euclidean divisions operate only on that smaller width.
      return match arithmetic with
        | .word => small + 1
        | .bits => 2 * leftWidth * rightWidth + small * small * small + 1
  | some ("math", "isqrt"), [value] => do
      let value ← scalarNumber value
      let width := bitLength value
      return match arithmetic with | .word => width | .bits => width * width * width
  | _, _ => none

def primitive (arithmetic : Arithmetic) (operation : Primitive) (values : List Constant) : Option Nat :=
  match operation, values with
  | .raiseException _, values => some (values.length + 1)
  | .builtin .identity, [_, _] | .builtin .isinstanceInt, [_] => some 1
  | .builtin .len, [.string _] | .builtin .len, [.bytes _] => some 1
  | .builtin .abs, [value] => integerWork arithmetic value
  | .builtin .intBitLength, [value] => integerWork arithmetic value
  | .builtin .pow, [left, right] => binary arithmetic .pow left right
  | .builtin .max, values | .builtin .min, values =>
      some ((values.length + 1) * argumentWork arithmetic values)
  | .builtin .str, [.int value] => some (decimalOutput arithmetic value)
  | .builtin .str, [.string _] => some 1
  | .builtin .str, [.bool _] | .builtin .str, [.none] | .builtin .str, [] => some 1
  | .builtin .repr, [value] =>
      let size := scalarSize .bits value
      some (size * size + 1)
  | .builtin .bin, [value] => do
      let value ← scalarNumber value
      return bitLength value + 1
  | .builtin .int, [.int _] | .builtin .int, [.bool _] | .builtin .int, [] => some 1
  | .builtin .int, [.string value] => some ((value.length + 1) * (value.length + 1))
  | .builtin .int, [.bytes value] => some ((value.length + 1) * (value.length + 1))
  | .subscript, [.string _, index] | .subscript, [.bytes _, index] =>
      (integerWork arithmetic index).map (· + 1)
  | .slice, [.string _, lower, upper, stride]
  | .slice, [.bytes _, lower, upper, stride] =>
      -- Charging the whole input is conservative even for an empty slice.
      some (argumentWork arithmetic values + scalarSize arithmetic lower +
        scalarSize arithmetic upper + scalarSize arithmetic stride)
  | _, _ => none

/-- Every branch that executes scalar arithmetic has a separate tariff.
The remaining branches only move references, inspect tags, or enter source code. -/
def charge (arithmetic : Arithmetic) (module : Module) (state : State) : Option Nat :=
  match state.work with
  | .primitive operation values => (primitive arithmetic operation values).map (· + 1)
  | .invoke name values =>
      if (findFunctionIn module.body name).isSome then some (values.length + 1)
      else (library arithmetic module name values).map (· + 1)
  | .startRange _ values _ _ _ _ | .startSum _ _ _ values _ =>
      some (argumentWork arithmetic values)
  | .startExtremum _ _ _ => none
  | .sumLoop sum next _ => some (rangeWork arithmetic next sum.stop sum.stride)
  | .extremumLoop _ _ _ => none
  | .block (.rangeStepLoop _ next stop stride _ _ :: _) _ =>
      some (rangeWork arithmetic next stop stride)
  | .block _ _ => some 1
  | .expr expression _ => match expression with
      | .builtinCall _ _ | .subscript _ _ | .extremumRange _ _ _ | .sumRange _ _ _ _
      | .constant _ | .name _ | .binOp _ _ _ | .unaryOp _ _ | .compare _ _
      | .boolOp _ _ | .ifExp _ _ _ | .call (.name _) _
      | .call (.attribute (.name _) _) _ => some 1
      | _ => none
  | .value value => match state.stack with
      | .binaryRight op left :: _ => (binary arithmetic op left value).map (· + 1)
      | .compareRight _ left :: _ | .chainRight _ left _ _ :: _ =>
          some (PrimitiveWork.comparison arithmetic left value + 1)
      | .unary .not :: _ => some 1
      | .unary .uSub :: _ | .unary .invert :: _ => (integerWork arithmetic value).map (· + 1)
      | .sumFilter sum next _ :: _ =>
          some (integer arithmetic next + integer arithmetic sum.stride + 1)
      | .sumElement sum next total :: _ => do
          let value ← scalarNumber value
          return integer arithmetic next + integer arithmetic sum.stride +
            integer arithmetic total + integer arithmetic value + 1
      | .extremumKey _ _ _ :: _ => none
      | .arguments _ done _ _ :: _ | .primitiveArguments _ done _ _ :: _
      | .rangeArguments _ done _ _ _ _ _ :: _ | .sumArguments _ _ _ done _ _ :: _
      | .extremumArguments _ _ done _ _ :: _ => some (done.length + 1)
      | .unpack names done _ _ _ :: _ => some (names.length + done.length + 1)
      | [] | .binaryLeft _ _ _ :: _ | .compareLeft _ _ _ :: _ | .chainLeft _ _ _ _ :: _
      | .boolean _ _ _ :: _ | .conditional _ _ _ :: _ | .assign _ _ _ :: _
      | .branch _ _ _ _ :: _ | .discard _ _ :: _ | .assertion _ _ _ :: _
      | .assertionMessage :: _ => some 1

def TimeBound (arithmetic : Arithmetic) (module : Module) (name : String)
    (values : List Constant) (bound : Nat) : Prop :=
  RuntimeCost.TimeBound (function module name values) (charge arithmetic module) bound

def IsBigO (arithmetic : Arithmetic) (module : Module) (name : String)
    (inputs : ι → List Constant) (domain : ι → Prop) (size : ι → Nat) (bound : Nat → Nat) : Prop :=
  RuntimeCost.IsBigO (fun input => function module name (inputs input))
    (fun _ => charge arithmetic module) domain size bound

end FormalSW.PyAst.Calls.Runtime
