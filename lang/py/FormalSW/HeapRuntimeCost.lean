import lang.py.FormalSW.HeapMapWork
import lang.py.FormalSW.HeapSetWork
import lang.py.FormalSW.HeapSortWork
import lang.py.FormalSW.HeapBufferWork
import lang.py.FormalSW.HeapSequenceWork
import lang.py.FormalSW.CallsRuntimeCost
import lang.py.FormalSW.DynamicArrayWork
import lang.py.FormalSW.AmortizedRuntimeCost

/-! Operand-sensitive runtime costs for the heap interpreter. Lists use grow-only
dynamic arrays with doubling capacity; appends pay for copying at a resize.
Unused slots, heap addresses, and local bindings are abstract machine storage.
Unsupported operations have no tariff, including mutations that would invalidate
the grow-only capacity model. Dictionaries default to collision-chain worst case.
These prices describe the target representation, not Lean's semantic lists. -/
namespace FormalSW.PyAst.HeapCalls.Runtime
open PrimitiveWork

def scalarValues (values : List Value) : Option (List Constant) :=
  values.mapM fun value => match value with | .scalar value => some value | .ref _ => none

/-- Pointer copying does not recursively copy the objects being referenced. -/
def sequenceLength (heap : Heap) : Value → Option Nat
  | .scalar (.string text) => some text.length
  | .scalar (.bytes bytes) => some bytes.length
  | .ref address => match heap[address]? with
      | some (.list items) | some (.tuple items) => some items.length
      | some (.bytearray items) => some items.length
      | _ => none
  | _ => none

def elementComparison (arithmetic : Arithmetic) : Value → Value → Option Nat
  | .scalar left, .scalar right => some (PrimitiveWork.comparison arithmetic left right)
  | .ref left, .ref right => if left = right then some 1 else none
  | _, _ => some 1

def sequenceComparison (arithmetic : Arithmetic) : List Value → List Value → Option Nat
  | [], _ | _, [] => some 1
  | left :: ls, right :: rs => do
      return (← elementComparison arithmetic left right) + (← sequenceComparison arithmetic ls rs) + 1

def comparison (arithmetic : Arithmetic) (heap : Heap) (op : CmpOp) (left right : Value) : Option Nat :=
  match left, right with
  | .scalar left, .scalar right => some (PrimitiveWork.comparison arithmetic left right)
  | .ref left, .ref right =>
      match op, heap[left]?, heap[right]? with
      | .eq, some (.list ls), some (.list rs)
      | .notEq, some (.list ls), some (.list rs) =>
          if left = right ∨ ls.length ≠ rs.length then some 1 else sequenceComparison arithmetic ls rs
      | _, _, _ => none
  | _, _ => none

/-- Type/length metadata suffices for truth of builtin scalars and containers. -/
def truth (heap : Heap) : Value → Option Nat
  | .scalar _ => some 1
  | .ref address => match heap[address]? with
      | some (.list _) | some (.tuple _) | some (.bytearray _)
      | some (.dict _) | some (.set _) | some (.keyDict _) | some (.keySet _) => some 1
      | _ => none

def operation (arithmetic : Arithmetic) (heap : Heap) (op : Operation) (values : List Value)
    (maps : MapRepresentation := .collisionChain) : Option Nat :=
  match op, values with
  | .list, values | .tuple, values => some (sequenceCopy values.length)
  | .append address, [_] => match heap[address]? with
      | some (.list items) => some (DynamicArray.append items.length)
      | _ => none
  | .reversedList, [value] | .builtin .list, [value] =>
      (sequenceLength heap value).map sequenceCopy
  | .builtin .list, [] => some 1
  | .builtin .len, [value] => (sequenceLength heap value).map (fun _ => 1)
  | .slice, [.ref address, lower, upper, stride] => match heap[address]? with
      | some (.list items) => SequenceWork.slice arithmetic items.length lower upper stride
      | _ => none
  | .subscript, [.ref address, .scalar index] =>
      match heap[address]? with
      | some (.list items) | some (.tuple items) => do
          let index ← scalarNumber index
          return integer arithmetic index + integer arithmetic items.length + 1
      | _ => BufferWork.operation arithmetic heap op values <|> MapWork.operation maps arithmetic heap op values
  | .builtin .bytearray, values => BufferWork.operation arithmetic heap op values
  | .builtin .set, [] => SetWork.operation maps arithmetic heap op values
  | .builtin .sorted, values => SortWork.operation arithmetic heap values
  | .add _, _ => SetWork.operation maps arithmetic heap op values
  | .builtin .max, [.ref _] | .builtin .min, [.ref _] =>
      SetWork.operation maps arithmetic heap op values
  | .builtin builtin, values => do
      Calls.Runtime.primitive arithmetic (.builtin builtin) (← scalarValues values)
  | .raiseException name, values => do
      Calls.Runtime.primitive arithmetic (.raiseException name) (← scalarValues values)
  | _, _ => BufferWork.operation arithmetic heap op values <|> MapWork.operation maps arithmetic heap op values

def charge (arithmetic : Arithmetic) (module : Module) (state : State)
    (maps : MapRepresentation := .collisionChain) : Option Nat :=
  match state.work with
  | .operation (.call name) values =>
      match findFunctionIn module.body name with
      | some (args, _) => some (values.length + args.length + 1)
      | none => do
          let values ← scalarValues values
          (Calls.Runtime.library arithmetic module name values).map (· + 1)
  | .operation op values => (operation arithmetic state.heap op values maps).map (· + 1)
  | .startRange _ values _ _ _ _ => do
      return Calls.Runtime.argumentWork arithmetic (← scalarValues values)
  | .block body _ => match body with
      | .rangeStepLoop _ next stop stride _ _ :: _ => some (Calls.Runtime.rangeWork arithmetic next stop stride)
      | .sequenceStepLoop _ (.ref address) position _ _ :: _ => match state.heap[address]? with
          | some (.list items) | some (.tuple items) =>
              some (2 + 2 * integer arithmetic position + integer arithmetic items.length)
          | _ => none
      | .enumerateStepLoop _ _ (.ref address) position counter _ _ :: _ => match state.heap[address]? with
          | some (.bytearray bytes) =>
              some (3 + 2 * integer arithmetic position + integer arithmetic counter + integer arithmetic bytes.length)
          | _ => none
      | .assign [.tuple targets] _ :: _ | .assign [.list targets] _ :: _ =>
          (Calls.targetNames targets).map (fun _ => targets.length + 1)
      | .raise (some (.call (.name _) _)) :: _ | .raise (some (.name _)) :: _ => some 1
      | [] | .assign [.name _] _ :: _ | .augAssign (.name _) _ _ :: _
      | .assign [.subscript _ _] _ :: _
      | .return _ :: _ | .ifThen _ _ _ :: _ | .whileDo _ _ _ :: _
      | .assert _ _ :: _
      | .forIn (.name _) _ _ _ :: _
      | .forIn (.tuple [.name _, .name _]) (.call (.name "enumerate") [_]) _ _ :: _
      | .expr _ :: _ | .loopResume _ :: _ | .breakLoop :: _ | .continueLoop :: _ => some 1
      | _ => none
  | .expr expression _ => match expression with
      | .call (.attribute _ "append") [_] | .call (.attribute _ "add") [_] => some 1
      | .constant _ | .name _ | .binOp _ _ _ | .unaryOp _ _ | .compare _ _
      | .boolOp _ _ | .ifExp _ _ _ | .call (.name _) _
      | .builtinCall _ _
      | .list _ | .tuple _ | .reversedList _ | .subscript _ _ => some 1
      | .call (.attribute (.name _) _) _ => some 1
      | _ => none
  | .value value => match state.stack with
      | .binaryRight .add (.ref address) false :: _ =>
          (SequenceWork.concatenate arithmetic state.heap (.ref address) value).map (· + 1)
      | .binaryRight op (.scalar left) _ :: _ => match value with
          | .scalar right => (PrimitiveWork.binary arithmetic op left right).map (· + 1)
          | _ => (BufferWork.repetition arithmetic state.heap op (.scalar left) value).map (· + 1)
      | .binaryRight op (.ref address) _ :: _ =>
          (BufferWork.repetition arithmetic state.heap op (.ref address) value).map (· + 1)
      | .compareRight op left :: _ | .chainRight op left _ _ :: _ =>
          (comparison arithmetic state.heap op left value).map (· + 1)
      | .unary .not :: _ => truth state.heap value
      | .unary .uSub :: _ | .unary .invert :: _ => match value with
          | .scalar value => (Calls.Runtime.integerWork arithmetic value).map (· + 1)
          | _ => none
      | .boolean _ _ _ :: _ | .conditional _ _ _ :: _ | .branch _ _ _ _ :: _
      | .assertion _ _ _ :: _
      | .chainResult _ _ _ :: _ => truth state.heap value
      | .arguments _ done _ _ :: _ | .rangeArguments _ done _ _ _ _ _ :: _ => some (done.length + 1)
      | .enumerateStart _ _ (.ref address) _ _ _ _ :: _ => match state.heap[address]?, value with
          | some (.bytearray _), .scalar value => (scalarNumber value).map (fun initial => 2 + integer arithmetic initial)
          | _, _ => none
      | .appendReceiver _ _ :: _ => match value with
          | .ref address => match state.heap[address]? with
              | some (.list _) => some 1
              | _ => none
          | _ => none
      | .addReceiver _ _ :: _ => match value with
          | .ref address => match state.heap[address]? with
              | some (.set _) => some 1
              | _ => none
          | _ => none
      | .unpack names _ _ :: _ =>
          (sequenceLength state.heap value).map (fun length => length + names.length + 1)
      | .sequence _ _ _ _ _ :: _ => match value with
          | .ref address => match state.heap[address]? with
              | some (.list _) | some (.tuple _) => some 1
              | _ => none
          | _ => none
      | [] | .binaryLeft _ _ _ _ :: _ | .compareLeft _ _ _ :: _ | .chainLeft _ _ _ _ :: _
      | .assign _ _ _ :: _ | .discard _ _ :: _
      | .enumerateSource _ _ _ _ _ _ _ :: _
      | .assignItem _ _ _ _ :: _ | .assignSlice _ _ _ _ _ _ :: _ => some 1
      | _ => none
  | _ => none

def objectPotential : Mutable.Object → Nat
  | .list items => DynamicArray.potential items.length
  | _ => 0

def heapPotential (heap : Heap) : Nat := (heap.map objectPotential).sum

def potential (state : State) : Nat := heapPotential state.heap

def TimeBound (arithmetic : Arithmetic) (module : Module) (name : String)
    (values : List Value) (heap : Heap) (bound : Nat)
    (maps : MapRepresentation := .collisionChain) : Prop :=
  RuntimeCost.TimeBound (call module name values heap).execution (fun state => charge arithmetic module state maps) bound

/-- A uniform bound on complete source executions, with every heap operation priced. -/
def IsBigO (arithmetic : Arithmetic) (module : Module) (name : String)
    (inputs : ι → List Value) (heaps : ι → Heap) (domain : ι → Prop)
    (size : ι → Nat) (bound : Nat → Nat) (maps : MapRepresentation := .collisionChain) : Prop :=
  RuntimeCost.IsBigO (fun input => (call module name (inputs input) (heaps input)).execution)
    (fun _ state => charge arithmetic module state maps) domain size bound

end FormalSW.PyAst.HeapCalls.Runtime
