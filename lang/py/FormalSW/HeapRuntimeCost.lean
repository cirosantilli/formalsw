import lang.py.FormalSW.HeapMapWork
import lang.py.FormalSW.HeapRecordWork
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

/-- Shallow extension reads the source and writes through a grow-only array.
The read allowance also covers snapshotting a receiver extended with itself. -/
def listExtension (heap : Heap) (address : Nat) : Value → Option Nat
  | .ref source => match heap[address]?, heap[source]? with
      | some (.list items), some (.list additional) =>
          some (DynamicArray.appendMany items.length additional.length + additional.length + 1)
      | _, _ => none
  | _ => none

/-- A destructuring iterator reads one live item, copies its fields and assigns
the targets. Exhaustion only reads the receiver's length. -/
def unpackIteration (arithmetic : Arithmetic) (heap : Heap) (names : List String)
    (address position : Nat) : Option Nat := do
  let items ← match heap[address]? with
    | some (.list items) | some (.tuple items) => some items
    | _ => none
  let traversal := 2 + 2*integer arithmetic position + integer arithmetic items.length
  match items[position]? with
  | none => return traversal
  | some value =>
      let fields ← sequenceLength heap value
      return traversal + fields + names.length + integer arithmetic fields + 1

/-- Zip retains its builtin receivers. Each advance reads up to one item from
each receiver and allocates a tuple containing the obtained references. -/
def zipIteration (arithmetic : Arithmetic) (heap : Heap)
    (sources : List SequenceSource) (position : Nat) : Option Nat := do
  let widths ← sources.mapM fun source => do
    let length ← sequenceLength heap (sequenceValue source)
    return 2 + integer arithmetic position + integer arithmetic length
  return widths.sum + 2*sources.length + 2

def elementComparison (arithmetic : Arithmetic) : Value → Value → Option Nat
  | .scalar left, .scalar right => some (PrimitiveWork.comparison arithmetic left right)
  | .ref left, .ref right => if left = right then some 1 else none
  | _, _ => some 1

def sequenceComparison (arithmetic : Arithmetic) : List Value → List Value → Option Nat
  | [], _ | _, [] => some 1
  | left :: ls, right :: rs => do
      return (← elementComparison arithmetic left right) + (← sequenceComparison arithmetic ls rs) + 1

/-- A conservative linear scan, including the comparisons of scalar contents. -/
def sequenceMembership (arithmetic : Arithmetic) (needle : Value) : List Value → Option Nat
  | [] => some 1
  | item :: rest => do
      return (← elementComparison arithmetic item needle) + (← sequenceMembership arithmetic needle rest) + 1

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
  | .method _ args _, values => some (values.length + args.length + 1)
  | .setField name _, [receiver] => RecordWork.write heap receiver name
  | .list, values | .tuple, values => some (sequenceCopy values.length)
  | .comprehension _ ((_, .call (.name "range") _, _) :: _) _, values =>
      (scalarValues values).map (fun values => Calls.Runtime.argumentWork arithmetic values + 1)
  | .comprehension _ (_ :: _) _, [source] => (sequenceLength heap source).map (fun _ => 2)
  | .comprehensionTargets _ ((_, .zipIterable _, _) :: _) _, values => do
      let _ ← values.mapM (sequenceLength heap)
      return 2*values.length + 1
  | .sumSequence, [source, .scalar (.int initial)] =>
      -- Iterator acquisition uses builtin metadata. The lowered loop separately
      -- charges each element read and addition, without copying the input.
      (sequenceLength heap source).map (fun _ => integer arithmetic initial + 1)
  | .sumGenerator _ [(_, .call (.name "range") _, _)] _ _, values =>
      (scalarValues values).map (fun values => Calls.Runtime.argumentWork arithmetic values + 1)
  | .sumGenerator _ [(_, _, [])] _ _, [source] =>
      (sequenceLength heap source).map (fun _ => 2)
  | .append address, [_] => match heap[address]? with
      | some (.list items) => some (DynamicArray.append items.length)
      | _ => none
  | .reversedList, [value] | .builtin .list, [value] =>
      (sequenceLength heap value).map sequenceCopy
  | .builtin .list, [] => some 1
  | .builtin .len, [value] => (sequenceLength heap value).map (fun _ => 1)
  | .membership _, [needle, .ref address] => match heap[address]? with
      | some (.list items) | some (.tuple items) => sequenceMembership arithmetic needle items
      | _ => BufferWork.operation arithmetic heap op values <|> MapWork.operation maps arithmetic heap op values
  | .slice, [.ref address, lower, upper, stride] => match heap[address]? with
      | some (.list items) => SequenceWork.slice arithmetic items.length lower upper stride
      | _ => none
  | .slice, [.scalar value, .scalar lower, .scalar upper, .scalar stride] =>
      Calls.Runtime.primitive arithmetic .slice [value, lower, upper, stride]
  | .subscript, [.scalar value, .scalar index] =>
      Calls.Runtime.primitive arithmetic .subscript [value, index]
  | .subscript, [.ref address, .scalar index] =>
      match heap[address]? with
      | some (.list items) | some (.tuple items) => do
          let index ← scalarNumber index
          return integer arithmetic index + integer arithmetic items.length + 1
      | _ => BufferWork.operation arithmetic heap op values <|> MapWork.operation maps arithmetic heap op values
  | .builtin .bytearray, values => BufferWork.operation arithmetic heap op values
  | .builtin .set, [] => SetWork.operation maps arithmetic heap op values
  | .builtin .sorted, values => SortWork.operation arithmetic heap values
  | .builtin .divmod, [.scalar (.int left), .scalar (.int right)] => do
      return (← PrimitiveWork.binary arithmetic .floorDiv (.int left) (.int right)) +
        (← PrimitiveWork.binary arithmetic .mod (.int left) (.int right)) + sequenceCopy 2
  | .add _, _ => SetWork.operation maps arithmetic heap op values
  | .builtin .max, [.ref address] | .builtin .min, [.ref address] =>
      match heap[address]? with
      | some (.list items) | some (.tuple items) =>
          (scalarValues items).map (SetWork.extremum arithmetic)
      | _ => SetWork.operation maps arithmetic heap op values
  | .builtin builtin, values => do
      Calls.Runtime.primitive arithmetic (.builtin builtin) (← scalarValues values)
  | .raiseException name, values => do
      Calls.Runtime.primitive arithmetic (.raiseException name) (← scalarValues values)
  | _, _ => BufferWork.operation arithmetic heap op values <|> MapWork.operation maps arithmetic heap op values

def unpackEntry (targets : List Expr) (iterable : Expr) : Option Nat :=
  match iterable with
  | .call (.name "enumerate") [_] => match targets with
      | [.name _, .name _] => some 1
      | _ => (Calls.targetNames targets).map (fun _ => targets.length + 1)
  | _ => (Calls.targetNames targets).map (fun _ => targets.length + 1)

def attributeCallEntry (base : Expr) (name : String) (args : List Expr) : Option Nat :=
  if name = "get" ∨ ((name = "append" ∨ name = "add") ∧ args.length = 1) then some 1
  else match base with | .name _ => some 1 | _ => none

@[simp] theorem attributeCallEntry_name (receiver name : String) (args : List Expr) :
    attributeCallEntry (.name receiver) name args = some 1 := by
  simp [attributeCallEntry]

def charge (arithmetic : Arithmetic) (module : Module) (state : State)
    (maps : MapRepresentation := .collisionChain) : Option Nat :=
  match state.work with
  | .dictionary [] entries _ => some (entries.length + 1)
  | .dictionary (_ :: _) _ _ => some 1
  | .operation (.call name) values =>
      match findFunctionIn module.body name with
      | some (args, _) => some (values.length + args.length + 1)
      | none => match libraryFunction module name with
          | some _ => do
              let scalar ← scalarValues values
              (Calls.Runtime.library arithmetic module name scalar).map (· + 1)
          | none => (RecordWork.construct module name values).map (· + 1)
  | .operation op values => (operation arithmetic state.heap op values maps).map (· + 1)
  | .startRange _ values _ _ _ _ => do
      return Calls.Runtime.argumentWork arithmetic (← scalarValues values)
  | .block body _ => match body with
      | .unpackStepLoop names (.ref address) position _ _ :: _ =>
          unpackIteration arithmetic state.heap names address position
      | .zipStepLoop _ sources position _ _ :: _ => zipIteration arithmetic state.heap sources position
      | .rangeStepLoop _ next stop stride _ _ :: _ => some (Calls.Runtime.rangeWork arithmetic next stop stride)
      | .sequenceStepLoop _ (.ref address) position _ _ :: _ => match state.heap[address]? with
          | some (.list items) | some (.tuple items) =>
              some (2 + 2 * integer arithmetic position + integer arithmetic items.length)
          | _ => none
      | .sequenceStepLoop _ (.scalar (.string text)) position _ _ :: _ =>
          some (2 + 2 * integer arithmetic position + integer arithmetic text.length)
      | .enumerateStepLoop _ _ (.ref address) position counter _ _ :: _ => match state.heap[address]? with
          | some (.bytearray bytes) =>
              some (3 + 2 * integer arithmetic position + integer arithmetic counter + integer arithmetic bytes.length)
          | _ => none
      | .assign [.tuple targets] _ :: _ | .assign [.list targets] _ :: _ =>
          (Calls.targetNames targets).map (fun _ => targets.length + 1)
      | .raise (some (.call (.name _) _)) :: _ | .raise (some (.name _)) :: _ => some 1
      | [] | .assign [.name _] _ :: _ | .augAssign (.name _) _ _ :: _
      | .annAssign (.name _) _ _ :: _
      | .assign [.attribute _ _] _ :: _ | .annAssign (.attribute _ _) _ _ :: _
      | .assign [.subscript _ _] _ :: _
      | .return _ :: _ | .ifThen _ _ _ :: _ | .whileDo _ _ _ :: _
      | .assert _ _ :: _
      | .forIn (.name _) _ _ _ :: _
      | .expr _ :: _ | .loopResume _ :: _ | .breakLoop :: _ | .continueLoop :: _ => some 1
      | .forIn (.tuple targets) iterable _ _ :: _ => unpackEntry targets iterable
      | .forIn (.list targets) _ _ _ :: _ =>
          (Calls.targetNames targets).map (fun _ => targets.length+1)
      | .comprehensionAppend _ _ :: _ => some 1
      | _ => none
  | .expr expression _ => match expression with
      | .call (.attribute base name) args => attributeCallEntry base name args
      | .constant _ | .name _ | .binOp _ _ _ | .unaryOp _ _ | .compare _ _
      | .boolOp _ _ | .ifExp _ _ _ | .call (.name _) _
      | .builtinCall _ _
      | .list _ | .tuple _ | .dict _ | .reversedList _ | .subscript _ _ | .sumSequence _ _
      | .membership _ _ _ | .attribute _ _ => some 1
      | .sumGenerator _ [_] _ | .sumRange _ _ _ _ => some 1
      | .listComp _ (_ :: _) | .listCompTargets _ (_ :: _) => some 1
      | _ => none
  | .value value => match state.stack with
      | .methodReceiver name _ _ :: _ =>
          (RecordWork.method module state.heap value name).map (· + 1) <|>
            (match name, value with
            | "get", .ref address => match state.heap[address]? with
                | some (.dict _) => some 1
                | _ => none
            | _, _ => none)
      | .dictionaryKey _ _ _ _ :: _ => match value with
          | .scalar _ => some 1
          | _ => none
      | .dictionaryValue key _ entries _ :: _ =>
          -- Search the current table, write the reference, and advance the frame.
          some (mapLookup maps entries.length (MapWork.keyWork arithmetic entries key) + 2)
      | .assignAttribute _ _ _ _ :: _ | .initialized _ :: _ => some 1
      | .unpackSequence _ _ _ _ _ :: _ => (sequenceLength state.heap value).map (fun _ => 1)
      | .attribute name :: _ => (RecordWork.field state.heap value name).map (· + 1)
      | .binaryRight .add (.ref address) false :: _ =>
          (SequenceWork.concatenate arithmetic state.heap (.ref address) value).map (· + 1)
      | .binaryRight .add (.ref address) true :: _ =>
          (listExtension state.heap address value).map (· + 1)
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
      | .sumStart _ _ :: _ => match value with
          | .scalar (.int initial) => some (integer arithmetic initial + 1)
          | _ => none
      | .generatorEnd :: _ => some 1
      | .comprehensionResult _ :: _ => some 1
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
    (maps : MapRepresentation := .collisionChain) (globals : Mutable.Globals := []) : Prop :=
  RuntimeCost.TimeBound (call module name values heap globals).execution (fun state => charge arithmetic module state maps) bound

/-- A uniform bound on complete source executions, with every heap operation priced. -/
def IsBigO (arithmetic : Arithmetic) (module : Module) (name : String)
    (inputs : ι → List Value) (heaps : ι → Heap) (domain : ι → Prop)
    (size : ι → Nat) (bound : Nat → Nat) (maps : MapRepresentation := .collisionChain)
    (globals : ι → Mutable.Globals := fun _ => []) : Prop :=
  RuntimeCost.IsBigO (fun input => (call module name (inputs input) (heaps input) (globals input)).execution)
    (fun _ state => charge arithmetic module state maps) domain size bound

end FormalSW.PyAst.HeapCalls.Runtime
