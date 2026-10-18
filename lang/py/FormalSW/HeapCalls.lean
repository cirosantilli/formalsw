import lang.py.FormalSW.Instances
import lang.py.FormalSW.Linking
import lang.py.FormalSW.ScalarSort

/-! Function calls with shared lists. Locals and continuations carry references;
all frames use one heap, including when a helper raises after mutating a list. -/
namespace FormalSW.PyAst.HeapCalls
abbrev Value := Mutable.Value
abbrev Heap := Mutable.Heap
abbrev Env := Mutable.Env
abbrev Eval := Mutable.Eval
abbrev Completion := Mutable.Completion

/-- Rebinding a local never copies its referenced object. -/
def setLocal (env : Env) (name : String) (value : Value) : Env :=
  fun query => if query = name then some value else env query

/-- Flat unpacking assigns names left to right after validating the whole sequence. -/
def assignNames (env : Env) (names : List String) (values : List Value) : Env :=
  (names.zip values).foldl (fun env (name, value) => setLocal env name value) env

def argumentEnv (args : List Arg) (values : List Value) : Env :=
  fun name => ((args.map Arg.name).zip values).lookup name

def completeArguments : List Arg → List Value → Option (List Value)
  | [], [] => some []
  | [], _ :: _ => none
  | arg :: args, [] => do
      let value ← arg.defaultValue
      return .scalar value :: (← completeArguments args [])
  | _ :: args, value :: values => do
      return value :: (← completeArguments args values)

/-- A scalar operation runs in the same heap without allocating an object. -/
def scalarResult (result : Option (Except ExceptionObject Constant)) : Eval Value :=
  match result with
  | none => Mutable.unsupported
  | some (.error error) => throw error
  | some (.ok value) => pure (.scalar value)

def unary (op : UnaryOp) (value : Value) : Eval Value := do
  match op with
  | .not => return .scalar (.bool (!(← Mutable.truth value)))
  | .uSub => match value with
      | .scalar value => scalarResult (scalarExpr (fun _ => none) (.unaryOp .uSub (.constant value)))
      | .ref _ => Mutable.error "TypeError"

/-- Scalar element equality uses Python's numeric coercion. References with the
same identity compare equal; comparisons of distinct nested lists are partial. -/
def equalElements : List Value → List Value → Option Bool
  | [], [] => some true
  | a :: as, b :: bs => do
      let equal ← match a, b with
        | .scalar a, .scalar b => scalarCompare .eq a b
        | .ref a, .ref b => if a = b then some true else none
        | _, _ => some false
      if equal then equalElements as bs else some false
  | _, _ => some false

def equalLists (left right : List Value) : Option Bool :=
  if left.length = right.length then equalElements left right else some false

theorem equalElements_ints (left right : List Int) :
    equalElements (left.map fun n => .scalar (.int n)) (right.map fun n => .scalar (.int n)) =
      some (decide (left = right)) := by
  induction left generalizing right with
  | nil => cases right <;> simp [equalElements]
  | cons value rest ih =>
      cases right with
      | nil => simp [equalElements]
      | cons other tail =>
          by_cases same : value = other
          · subst other
            simp [equalElements, scalarCompare, evalCmpOp, ih]
          · simp [equalElements, scalarCompare, evalCmpOp, same]

theorem equalLists_ints (left right : List Int) :
    equalLists (left.map fun n => .scalar (.int n)) (right.map fun n => .scalar (.int n)) =
      some (decide (left = right)) := by
  by_cases lengths : left.length = right.length
  · simp [equalLists, lengths, equalElements_ints]
  · have different : left ≠ right := fun same => lengths (congrArg List.length same)
    simp [equalLists, lengths, different]

@[simp] def compareScalars (op : CmpOp) (left right : Constant) : Eval Value :=
  match scalarCompare op left right with
  | some value => pure (.scalar (.bool value))
  | none => Mutable.error "TypeError"

@[simp] def compareDifferent (op : CmpOp) : Eval Value :=
  match op with
  | .eq => pure (.scalar (.bool false))
  | .notEq => pure (.scalar (.bool true))
  | _ => Mutable.error "TypeError"

def compare (op : CmpOp) (left right : Value) : Eval Value := do
  match left, right with
  | .scalar a, .scalar b => compareScalars op a b
  | .ref a, .ref b =>
      match (← get)[a]?, (← get)[b]? with
      | some (.bytearray xs), some (.bytearray ys) => compareScalars op (.bytes xs) (.bytes ys)
      | some (.set xs), some (.set ys) => return .scalar (.bool (ScalarSet.compare op xs ys))
      | some (.instance _ _ _), some (.instance _ _ _) =>
          match op with
          | .eq => return .scalar (.bool (a == b))
          | .notEq => return .scalar (.bool (a != b))
          | _ => Mutable.error "TypeError"
      | some (.tuple xs), some (.tuple ys) =>
          match op with
          | .eq | .notEq =>
              let some equal := if a = b then some true else equalLists xs ys | Mutable.unsupported
              return .scalar (.bool (if op == .eq then equal else !equal))
          | _ => Mutable.unsupported
      | some (.list _), some (.list _) =>
          let (_, xs) ← Mutable.array left
          let (_, ys) ← Mutable.array right
          match op with
          | .eq | .notEq =>
              let some equal := if a = b then some true else equalLists xs ys | Mutable.unsupported
              return .scalar (.bool (if op == .eq then equal else !equal))
          | _ => Mutable.unsupported
      | none, _ | _, none => Mutable.unsupported
      | _, _ => compareDifferent op
  | .ref address, .scalar scalar =>
      match (← get)[address]?, scalar with
      | some (.bytearray bytes), .bytes other => compareScalars op (.bytes bytes) (.bytes other)
      | none, _ => Mutable.unsupported
      | _, _ => compareDifferent op
  | .scalar scalar, .ref address =>
      match scalar, (← get)[address]? with
      | .bytes bytes, some (.bytearray other) => compareScalars op (.bytes bytes) (.bytes other)
      | _, none => Mutable.unsupported
      | _, _ => compareDifferent op

theorem compare_int_lists (left right : List Int)
    (foundLeft : heap[a]? = some (.list (left.map fun n => .scalar (.int n))))
    (foundRight : heap[b]? = some (.list (right.map fun n => .scalar (.int n)))) :
    compare .eq (.ref a) (.ref b) heap = some (.ok (.scalar (.bool (decide (left = right)))), heap) := by
  by_cases same : a = b
  · subst b
    have encoded : (left.map fun n => Mutable.Value.scalar (.int n)) =
        right.map (fun n => Mutable.Value.scalar (.int n)) := Mutable.Object.list.inj (Option.some.inj (foundLeft.symm.trans foundRight))
    have injective : left = right := by
      clear foundLeft foundRight
      induction left generalizing right with
      | nil => cases right <;> simp_all
      | cons value rest ih =>
          cases right with
          | nil => simp at encoded
          | cons other tail =>
              simp only [List.map_cons, List.cons.injEq, Mutable.Value.scalar.injEq, Constant.int.injEq] at encoded
              rw [encoded.1, ih tail encoded.2]
    subst right
    simp [compare, Mutable.array, foundLeft, Except.map]
    rfl
  · simp [compare, Mutable.array, foundLeft, foundRight, same, equalLists_ints]
    rfl

/-- In-place list operations preserve the left reference. Scalar operations
fall back to ordinary binary evaluation. -/
private def listInplace (op : BinOp) (left right : Value) : Eval Value := do
  match left, right, op with
  | .ref address, .ref _, .add =>
      let items := (← Mutable.array left).2 ++ (← Mutable.sequence right)
      modify fun heap => heap.set address (.list (items))
      return left
  | .ref address, .scalar (.bytes bytes), .add =>
      let items := (← Mutable.array left).2 ++ bytes.map (fun byte => .scalar (.int byte.toNat))
      modify fun heap => heap.set address (.list items)
      return left
  | .ref address, .scalar (.string text), .add =>
      let items := (← Mutable.array left).2 ++ text.toList.map (fun c =>
        Mutable.Value.scalar (.string (String.singleton c)))
      modify fun heap => heap.set address (.list (items))
      return left
  | .ref address, .scalar (.int n), .mult =>
      let items := (List.replicate n.toNat (← Mutable.array left).2).flatten
      modify fun heap => heap.set address (.list (items))
      return left
  | .ref address, .scalar (.bool b), .mult =>
      let items := (← Mutable.array left).2
      modify fun heap => heap.set address (.list ((if b then items else [])))
      return left
  | _, _, _ => Mutable.binary op left right

/-- In-place buffer updates preserve the address observed by every alias. -/
def inplace (op : BinOp) (left right : Value) : Eval Value := do
  match left with
  | .scalar _ => Mutable.binary op left right
  | .ref address =>
      match (← get)[address]? with
      | none => Mutable.unsupported
      | some (.list _) => listInplace op left right
      | some (.set _) | some (.tuple _) | some (.instance _ _ _) => Mutable.binary op left right
      | some (.bytearray bytes) =>
          match op with
          | .mult =>
              let n ← Mutable.integer right
              modify fun heap => heap.set address (.bytearray (List.replicate n.toNat bytes).flatten)
              return left
          | .add =>
              let more ← match right with
                | .scalar (.bytes more) => pure more
                | .ref other =>
                    match (← get)[other]? with
                    | some (.bytearray more) =>
                        if other = address ∧ !more.isEmpty then Mutable.error "BufferError"
                        else pure more
                    | some (.list _) | some (.set _) | some (.tuple _) | some (.instance _ _ _) => Mutable.error "TypeError"
                    | none => Mutable.unsupported
                | _ => Mutable.error "TypeError"
              modify fun heap => heap.set address (.bytearray (bytes ++ more))
              return left
          | _ => Mutable.binary op left right

/-- List concatenation reads both lists before replacing the left object's contents. -/
theorem inplace_add_lists (heap : Heap) (left right : Nat) (leftItems rightItems : List Value)
    (leftFound : heap[left]? = some (.list leftItems))
    (rightFound : heap[right]? = some (.list rightItems)) :
    inplace .add (.ref left) (.ref right) heap =
      some (.ok (.ref left), heap.set left (.list (leftItems ++ rightItems))) := by
  simp [inplace, listInplace, Mutable.array, Mutable.sequence, leftFound, rightFound, Except.map]

inductive Operation where
  | call (name : String)
  /-- A bound function captures its receiver and definition before argument effects. -/
  | method (receiver : Value) (args : List Arg) (body : List Stmt)
  | notCallable
  | setField (name : String) (value : Value)
  | raiseException (typeName : String)
  | list
  | tuple
  | subscript
  | slice
  | setItem (replacement : Value)
  | setSlice (replacement : Value)
  | append (address : Nat)
  | add (address : Nat)
  | builtin (name : Builtin)
  | reversedList
  | sumSequence
  | sumGenerator (element : Expr) (generators : List (String × Expr × List Expr)) (env : Env) (start : Expr)
  | comprehension (element : Expr) (generators : List (String × Expr × List Expr)) (env : Env)

inductive Frame where
  | sumStart (loop : Stmt) (env : Env)
  | initialized (address : Nat)
  | attribute (name : String)
  | methodReceiver (name : String) (arguments : List Expr) (env : Env)
  | assignAttribute (base : Expr) (name : String) (rest : List Stmt) (env : Env)
  | augmentAttribute (name : String) (op : BinOp) (right : Expr) (rest : List Stmt) (env : Env)
  | writeAttribute (receiver : Value) (name : String) (rest : List Stmt) (env : Env)
  | comprehensionResult (address : Nat)
  | binaryLeft (op : BinOp) (right : Expr) (env : Env) (inPlace : Bool)
  | binaryRight (op : BinOp) (left : Value) (inPlace : Bool)
  | compareLeft (op : CmpOp) (right : Expr) (env : Env)
  | compareRight (op : CmpOp) (left : Value)
  | chainLeft (op : CmpOp) (right : Expr) (rest : List (CmpOp × Expr)) (env : Env)
  | chainRight (op : CmpOp) (left : Value) (rest : List (CmpOp × Expr)) (env : Env)
  | chainResult (right : Value) (rest : List (CmpOp × Expr)) (env : Env)
  | unary (op : UnaryOp)
  | boolean (op : BoolOp) (rest : List Expr) (env : Env)
  | conditional (yes no : Expr) (env : Env)
  | arguments (operation : Operation) (done : List Value) (rest : List Expr) (env : Env)
  /-- Resolve the bound method before evaluating its argument. -/
  | appendReceiver (item : Expr) (env : Env)
  | addReceiver (item : Expr) (env : Env)
  | assign (name : String) (rest : List Stmt) (env : Env)
  | unpack (names : List String) (rest : List Stmt) (env : Env)
  | branch (yes no rest : List Stmt) (env : Env)
  | discard (rest : List Stmt) (env : Env)
  | assertion (message : Option Expr) (rest : List Stmt) (env : Env)
  | assertionMessage
  | sequence (name : String) (body otherwise following : List Stmt) (env : Env)
  | unpackSequence (names : List String) (body otherwise following : List Stmt) (env : Env)
  | enumerateSource (index name : String) (start : Expr) (body otherwise following : List Stmt) (env : Env)
  | enumerateStart (index name : String) (source : Value) (body otherwise following : List Stmt) (env : Env)
  | assignItem (base index : Expr) (rest : List Stmt) (env : Env)
  | assignSlice (base lower upper stride : Expr) (rest : List Stmt) (env : Env)
  | rangeArguments (name : String) (done : List Value) (rest : List Expr)
      (body otherwise following : List Stmt) (env : Env)

inductive Work where
  | expr (expression : Expr) (env : Env)
  | block (body : List Stmt) (env : Env)
  | value (value : Value)
  | operation (operation : Operation) (values : List Value)
  | startRange (name : String) (values : List Value)
      (body otherwise following : List Stmt) (env : Env)

structure State where
  work : Work
  stack : List Frame
  heap : Heap

def done (anchors : Nat) (heap : Heap) (outcome : Except ExceptionObject Value) : Step State Completion :=
  .done (.ok ⟨outcome, [], heap, anchors⟩)

def run (anchors : Nat) (heap : Heap) (action : Eval α)
    (next : α → Heap → Step State Completion) : Step State Completion :=
  match action heap with
  | none => .unsupported
  | some (.error error, heap) => done anchors heap (.error error)
  | some (.ok value, heap) => next value heap

def result (anchors : Nat) (heap : Heap) (action : Eval Value) (stack : List Frame) : Step State Completion :=
  run anchors heap action fun value heap => .next ⟨.value value, stack, heap⟩

def argumentsState (operation : Operation) (env : Env) (done : List Value)
    (expressions : List Expr) (stack : List Frame) (heap : Heap) : State :=
  match expressions with
  | [] => ⟨.operation operation done, stack, heap⟩
  | first :: rest => ⟨.expr first env, .arguments operation done rest env :: stack, heap⟩

/-- Evaluate all range arguments before converting their values to indices. -/
def rangeBounds (values : List Value) : Except ExceptionObject (Int × Int × Int) := do
  let scalars ← values.mapM fun value => match value with
    | .scalar value => .ok value
    | .ref _ => .error { typeName := "TypeError", args := [] }
  Calls.rangeBounds scalars

private def rangeState (name : String) (env : Env) (done : List Value)
    (expressions : List Expr) (body otherwise following : List Stmt)
    (stack : List Frame) (heap : Heap) : State :=
  match expressions with
  | [] => ⟨.startRange name done body otherwise following env, stack, heap⟩
  | first :: rest =>
      ⟨.expr first env, .rangeArguments name done rest body otherwise following env :: stack, heap⟩

/-- The iterator retains the original reference even if its local is rebound. -/
def sequenceSource : Value → SequenceSource
  | .scalar value => .scalar value
  | .ref address => .ref address

def sequenceValue : SequenceSource → Value
  | .scalar value => .scalar value
  | .ref address => .ref address

@[simp] theorem sequenceValue_source (value : Value) :
    sequenceValue (sequenceSource value) = value := by cases value <;> rfl

/-- All targets are local to the comprehension, including targets in later loops.
The first iterable is evaluated separately in the enclosing environment. -/
def comprehensionEnv (env : Env) (generators : List (String × Expr × List Expr)) : Env :=
  fun name => if generators.any (fun generator => generator.1 == name) then none else env name

/-- Filters short-circuit in source order before entering the next loop. -/
def comprehensionFilters (filters : List Expr) (body : List Stmt) : List Stmt :=
  filters.foldr (fun condition rest => [.ifThen condition rest []]) body

/-- Reuse ordinary loop semantics, retaining live references to mutable iterables. -/
def comprehensionBody (address : Nat) (element : Expr) : List (String × Expr × List Expr) → List Stmt
  | [] => [.comprehensionAppend address element]
  | (name, iterable, filters) :: rest =>
      [.forIn (.name name) iterable
        (comprehensionFilters filters (comprehensionBody address element rest)) []]

/-- Validate the first iterator before allocating the private result list. -/
def comprehensionStart (anchors : Nat) (element : Expr)
    (generators : List (String × Expr × List Expr)) (env : Env)
    (values : List Value) (stack : List Frame) (heap : Heap) : Step State Completion :=
  match generators with
  | [] => .unsupported
  | (name, iterable, filters) :: rest =>
      let body := comprehensionFilters filters (comprehensionBody heap.length element rest)
      let enter := fun loop => Step.next
        ⟨.block [loop] env, .comprehensionResult heap.length :: stack, heap ++ [.list []]⟩
      match iterable with
      | .call (.name "range") _ => match rangeBounds values with
          | .ok (start, stop, stride) => enter (.rangeStepLoop name start stop stride body [])
          | .error error => done anchors heap (.error error)
      | _ => match values with
          | [value] => run anchors heap (Mutable.sequence value) fun _ heap =>
              .next ⟨.block [.sequenceStepLoop name (sequenceSource value) 0 body []] env,
                .comprehensionResult heap.length :: stack, heap ++ [.list []]⟩
          | _ => .unsupported

/-- These internal names cannot collide with Python identifiers. -/
def sumAccumulator : String := "$formalsw.sum"
def sumItem : String := "$formalsw.item"

/-- Sum uses ordinary addition, never in-place mutation of its starting value. -/
def sumBody (element : Expr) : List (String × Expr × List Expr) → List Stmt
  | [] => [.assign [.name sumAccumulator] (.binOp (.name sumAccumulator) .add element)]
  | (name, iterable, filters) :: rest =>
      [.forIn (.name name) iterable (comprehensionFilters filters (sumBody element rest)) []]

/-- Python rejects textual starting values before requesting the first item. -/
def sumInitial (value : Value) : Eval Value := do
  match value with
  | .scalar (.string _) | .scalar (.bytes _) => Mutable.error "TypeError"
  | .ref address => match (← get)[address]? with
      | some (.bytearray _) => Mutable.error "TypeError"
      | none => Mutable.unsupported
      | _ => return value
  | _ => return value

def sumEnter (anchors : Nat) (loop : Stmt) (env : Env) (value : Value)
    (stack : List Frame) (heap : Heap) : Step State Completion :=
  run anchors heap (sumInitial value) fun value heap =>
    .next ⟨.block [loop, .return (.name sumAccumulator)] (setLocal env sumAccumulator value), stack, heap⟩

/-- Ordinary call arguments finish evaluating before the iterable is validated. -/
def sumSequenceStart (anchors : Nat) (values : List Value)
    (stack : List Frame) (heap : Heap) : Step State Completion :=
  match values with
  | [source, start] => run anchors heap (Mutable.sequence source) fun _ heap =>
      sumEnter anchors (.sequenceStepLoop sumItem (sequenceSource source) 0 (sumBody (.name sumItem) []) [])
        (fun _ => none) start stack heap
  | _ => .unsupported

/-- Generator creation validates its first iterator before evaluating the starting value.
Subsequent iterables, filters, and elements remain lazy. -/
def sumGeneratorStart (anchors : Nat) (element : Expr)
    (generators : List (String × Expr × List Expr)) (env : Env) (start : Expr)
    (values : List Value) (stack : List Frame) (heap : Heap) : Step State Completion :=
  match generators with
  | [] => .unsupported
  | (name, iterable, filters) :: rest =>
      let body := comprehensionFilters filters (sumBody element rest)
      let enter := fun loop heap => Step.next
        ⟨.expr start env, .sumStart loop (comprehensionEnv env generators) :: stack, heap⟩
      match iterable with
      | .call (.name "range") _ => match rangeBounds values with
          | .ok (first, stop, stride) => enter (.rangeStepLoop name first stop stride body []) heap
          | .error error => done anchors heap (.error error)
      | _ => match values with
          | [value] => run anchors heap (Mutable.sequence value) fun _ heap =>
              enter (.sequenceStepLoop name (sequenceSource value) 0 body []) heap
          | _ => .unsupported

/-- Enumerate accepts an integer start, including a Boolean, with no size limit. -/
def enumerateStart : Value → Eval Int
  | .scalar (.int value) => pure value
  | .scalar (.bool value) => pure (if value then 1 else 0)
  | _ => Mutable.error "TypeError"

def primitive : Operation → List Value → Eval Value
  | .notCallable, _ => Mutable.error "TypeError"
  | .setField name value, [receiver] => Mutable.writeField receiver name value
  | .raiseException typeName, values => do
      let args ← values.mapM fun value => match value with
        | .scalar value => pure value
        | .ref _ => Mutable.unsupported
      throw { typeName, args }
  | .list, values => Mutable.allocate values
  | .tuple, values => Mutable.allocateTuple values
  | .reversedList, [value] => do
      Mutable.allocate (← Mutable.sequence value).reverse
  | .subscript, [base, index] => Mutable.getItem base index
  | .slice, [base, lower, upper, stride] => Mutable.getSlice base lower upper stride
  | .setItem replacement, [base, index] => Mutable.setItem base index replacement
  | .setSlice replacement, [base, lower, upper, stride] => Mutable.setSlice base lower upper stride replacement
  | .append address, [value] => Mutable.appendItem address value
  | .add address, [value] => Mutable.addItem address value
  | .append _, _ | .add _, _ => Mutable.error "TypeError"
  | .builtin .len, [value] => Mutable.length value
  | .builtin .bytearray, values => Mutable.bytearray values
  | .builtin .set, [] => Mutable.allocateSet []
  | .builtin .sorted, [value] => do
      let items ← match value with
        | .ref address => match (← get)[address]? with
            | some (.set items) => pure (items.map Mutable.Value.scalar)
            | _ => Mutable.sequence value
        | _ => Mutable.sequence value
      let scalars ← items.mapM fun item => match item with
        | .scalar value => pure value
        | .ref _ => Mutable.unsupported
      match ScalarSort.sort scalars with
      | .ok values => Mutable.allocate (values.map Mutable.Value.scalar)
      | .error error => throw error
  | .builtin .intBitLength, [.scalar value] => scalarResult (some (Math.bitLengthCall value))
  | .builtin .intBitLength, [.ref _] => Mutable.error "AttributeError"
  | .builtin .int, [.ref address] => do
      match (← get)[address]? with
      | some (.bytearray bytes) => scalarResult (Calls.integerConversion [.bytes bytes])
      | some (.list _) | some (.set _) | some (.tuple _) | some (.instance _ _ _) => Mutable.error "TypeError"
      | _ => Mutable.unsupported
  | .builtin .int, values => do
      let values ← values.mapM fun value => match value with
        | .scalar value => pure value
        | .ref _ => Mutable.unsupported
      scalarResult (Calls.integerConversion values)
  | .builtin .str, values => do
      let values ← values.mapM fun value => match value with
        | .scalar value => pure value
        | .ref _ => Mutable.unsupported
      scalarResult (some (Strings.str values))
  | .builtin .max, [value] => do
      let items ← match value with
        | .ref address => match (← get)[address]? with
            | some (.set items) => pure (items.map Mutable.Value.scalar)
            | _ => Mutable.sequence value
        | _ => Mutable.sequence value
      let scalars ← items.mapM fun item => match item with
        | .scalar value => pure value
        | .ref _ => Mutable.unsupported
      scalarResult (some (ScalarSet.maximum scalars))
  | .builtin .max, values => do
      let values ← values.mapM fun value => match value with
        | .scalar value => pure value
        | .ref _ => Mutable.unsupported
      scalarResult (Calls.positionalMaximum values)
  | _, _ => Mutable.unsupported

private theorem mapM_identity (items : List Constant) :
    (items.mapM (fun value => pure value) : Eval (List Constant)) = pure items := by
  simpa using (List.mapM_pure (m := Eval) (l := items) (f := id))

/-- Sorting reads the list's current contents and returns a fresh list. -/
theorem primitive_sorted_list (heap : Heap) (address : Nat) (items sorted : List Constant)
    (found : heap[address]? = some (.list (items.map Mutable.Value.scalar)))
    (ordered : ScalarSort.sort items = .ok sorted) :
    primitive (.builtin .sorted) [.ref address] heap =
      some (.ok (.ref heap.length), heap ++ [.list (sorted.map Mutable.Value.scalar)]) := by
  simp [primitive, found, Mutable.sequence, List.mapM_map, mapM_identity,
    Function.comp_def, ordered, Mutable.allocate, Except.map]

theorem primitive_sorted_tuple (heap : Heap) (address : Nat) (items sorted : List Constant)
    (found : heap[address]? = some (.tuple (items.map Mutable.Value.scalar)))
    (ordered : ScalarSort.sort items = .ok sorted) :
    primitive (.builtin .sorted) [.ref address] heap =
      some (.ok (.ref heap.length), heap ++ [.list (sorted.map Mutable.Value.scalar)]) := by
  simp [primitive, found, Mutable.sequence, List.mapM_map, mapM_identity,
    Function.comp_def, ordered, Mutable.allocate, Except.map]

def library (module : Module) (name : String) (values : List Value) : Eval Value := do
  let some function := libraryFunction module name | Mutable.unsupported
  let scalars ← values.mapM fun value => match value with
    | .scalar scalar => pure scalar
    | .ref _ => Mutable.error "TypeError"
  scalarResult (some (function scalars))

/-- Validate the instance's nominal type before consulting its class definition. -/
def instanceClass (module : Module) (origin name : String) : Eval (List Stmt) :=
  match module.findClass name with
  | some (identity, body) => if identity = origin then pure body else Mutable.unsupported
  | none => Mutable.unsupported

/-- Method binding precedes argument evaluation, including failure and shadowing. -/
def bindMethod (module : Module) (receiver : Value) (name : String) : Eval Operation := do
  match receiver with
  | .ref address =>
      match (← get)[address]? with
      | some (.instance origin className fields) =>
          let body ← instanceClass module origin className
          if name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__" then Mutable.unsupported
          else match fields.lookup name with
          | some _ => pure .notCallable
          | none => match findFunctionIn body name with
              | some (args, body) => pure (.method receiver args body)
              | none => if name.startsWith "__" then Mutable.unsupported else Mutable.error "AttributeError"
      | some (.list _) | some (.bytearray _) =>
          if name = "append" then pure (.append address) else Mutable.unsupported
      | some (.set _) =>
          if name = "add" then pure (.add address)
          else if name = "append" then Mutable.error "AttributeError" else Mutable.unsupported
      | some (.tuple _) =>
          if name = "append" ∨ name = "add" then Mutable.error "AttributeError" else Mutable.unsupported
      | none => Mutable.unsupported
  | .scalar _ =>
      if name = "append" ∨ name = "add" then Mutable.error "AttributeError" else Mutable.unsupported

/-- Stored fields are values; first-class bound methods are outside this model. -/
def getAttribute (module : Module) (receiver : Value) (name : String) : Eval Value := do
  match receiver with
  | .scalar _ => Mutable.unsupported
  | .ref address => match (← get)[address]? with
      | some (.instance origin className fields) =>
          let body ← instanceClass module origin className
          if name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__" then Mutable.unsupported
          else match fields.lookup name with
            | some value => pure value
            | none =>
                if (findFunctionIn body name).isSome ∨ name.startsWith "__" then Mutable.unsupported
                else Mutable.error "AttributeError"
      -- Builtin attributes can be bound methods; no first-class method values yet.
      | _ => Mutable.unsupported

def invokeMethod (anchors : Nat) (receiver : Value) (args : List Arg) (body : List Stmt)
    (values : List Value) (stack : List Frame) (heap : Heap) : Step State Completion :=
  match completeArguments args (receiver :: values) with
  | some values => .next ⟨.block (executableBody body) (argumentEnv args values), stack, heap⟩
  | none => done anchors heap (.error { typeName := "TypeError", args := [] })

def construct (module : Module) (anchors : Nat) (name : String) (values : List Value)
    (stack : List Frame) (heap : Heap) : Step State Completion :=
  match module.findClass name with
  | none => .unsupported
  | some (origin, body) =>
      match findFunctionIn body "__init__" with
      | none => if values.isEmpty then result anchors heap (Mutable.allocateInstance origin name) stack
          else done anchors heap (.error { typeName := "TypeError", args := [] })
      | some (args, body) =>
          invokeMethod anchors (.ref heap.length) args body values (.initialized heap.length :: stack)
            (heap ++ [.instance origin name []])

def step (module : Module) (anchors : Nat) (state : State) : Step State Completion :=
  let ⟨work, stack, heap⟩ := state
  match work with
  | .startRange name values body otherwise following env =>
      match rangeBounds values with
      | .ok (start, stop, stride) =>
          .next ⟨.block (.rangeStepLoop name start stop stride body otherwise :: following) env, stack, heap⟩
      | .error error => done anchors heap (.error error)
  | .operation (.call name) values =>
      match findFunctionIn module.body name with
      | some (args, body) =>
          match completeArguments args values with
          | some values => .next ⟨.block (executableBody body) (argumentEnv args values), stack, heap⟩
          | none => done anchors heap (.error { typeName := "TypeError", args := [] })
      | none => match libraryFunction module name with
          | some _ => result anchors heap (library module name values) stack
          | none => construct module anchors name values stack heap
  | .operation (.method receiver args body) values =>
      invokeMethod anchors receiver args body values stack heap
  | .operation .sumSequence values => sumSequenceStart anchors values stack heap
  | .operation (.sumGenerator element generators env start) values =>
      sumGeneratorStart anchors element generators env start values stack heap
  | .operation (.comprehension element generators env) values =>
      comprehensionStart anchors element generators env values stack heap
  | .operation operation values => result anchors heap (primitive operation values) stack
  | .expr expression env =>
      match expression with
      | .constant value => .next ⟨.value (.scalar value), stack, heap⟩
      | .name name => match env name with
          | some value => .next ⟨.value value, stack, heap⟩
          | none => done anchors heap (.error { typeName := "UnboundLocalError", args := [] })
      | .attribute base field => .next ⟨.expr base env, .attribute field :: stack, heap⟩
      | .binOp a op b => .next ⟨.expr a env, .binaryLeft op b env false :: stack, heap⟩
      | .unaryOp op expression => .next ⟨.expr expression env, .unary op :: stack, heap⟩
      | .compare a [(op, b)] => .next ⟨.expr a env, .compareLeft op b env :: stack, heap⟩
      | .compare a ((op, b) :: rest) => .next ⟨.expr a env, .chainLeft op b rest env :: stack, heap⟩
      | .boolOp op (first :: rest) => .next ⟨.expr first env, .boolean op rest env :: stack, heap⟩
      | .ifExp test yes no => .next ⟨.expr test env, .conditional yes no env :: stack, heap⟩
      | .list expressions => .next (argumentsState .list env [] expressions stack heap)
      | .tuple expressions => .next (argumentsState .tuple env [] expressions stack heap)
      | .sumSequence iterable start =>
          .next (argumentsState .sumSequence env [] [iterable, start] stack heap)
      | .sumRange name element bounds filters =>
          .next ⟨.expr (.sumGenerator element [(name, .call (.name "range") bounds, filters)]
            (.constant (.int 0))) env, stack, heap⟩
      | .sumGenerator element (generators@((_, iterable, _) :: _)) start =>
          let expressions := match iterable with
            | .call (.name "range") expressions => expressions
            | _ => [iterable]
          .next (argumentsState (.sumGenerator element generators env start) env [] expressions stack heap)
      | .listComp element (generators@((_, iterable, _) :: _)) =>
          let expressions := match iterable with
            | .call (.name "range") expressions => expressions
            | _ => [iterable]
          .next (argumentsState (.comprehension element generators (comprehensionEnv env generators))
            env [] expressions stack heap)
      | .reversedList expression => .next (argumentsState .reversedList env [] [expression] stack heap)
      | .subscript base (.slice lower upper stride) =>
          .next (argumentsState .slice env [] [base, lower.getD (.constant .none),
            upper.getD (.constant .none), stride.getD (.constant .none)] stack heap)
      | .subscript base index => .next (argumentsState .subscript env [] [base, index] stack heap)
      | .builtinCall name expressions => .next (argumentsState (.builtin name) env [] expressions stack heap)
      | .call (.name name) expressions => .next (argumentsState (.call name) env [] expressions stack heap)
      | .call (.attribute base "append") [item] => .next ⟨.expr base env, .appendReceiver item env :: stack, heap⟩
      | .call (.attribute base "add") [item] => .next ⟨.expr base env, .addReceiver item env :: stack, heap⟩
      | .call (.attribute (.name name) field) args =>
          if (env name).isSome then
            .next ⟨.expr (.name name) env, .methodReceiver field args env :: stack, heap⟩
          else .next (argumentsState (.call (name ++ "." ++ field)) env [] args stack heap)
      | .call (.attribute base field) args =>
          .next ⟨.expr base env, .methodReceiver field args env :: stack, heap⟩
      | _ => .unsupported
  | .block body env =>
      match body with
      | [] => .next ⟨.value (.scalar .none), stack, heap⟩
      | .return expression :: _ => .next ⟨.expr expression env, stack, heap⟩
      | .raise (some (.call (.name typeName) args)) :: _ =>
          .next (argumentsState (.raiseException typeName) env [] args stack heap)
      | .raise (some (.name typeName)) :: _ =>
          .next (argumentsState (.raiseException typeName) env [] [] stack heap)
      | .assign [.subscript base (.slice lower upper stride)] expression :: rest =>
          .next ⟨.expr expression env, .assignSlice base (lower.getD (.constant .none))
            (upper.getD (.constant .none)) (stride.getD (.constant .none)) rest env :: stack, heap⟩
      | .assign [.subscript base index] expression :: rest =>
          .next ⟨.expr expression env, .assignItem base index rest env :: stack, heap⟩
      | .assign [.name name] expression :: rest => .next ⟨.expr expression env, .assign name rest env :: stack, heap⟩
      | .assign [.attribute base name] expression :: rest
        | .annAssign (.attribute base name) _ (some expression) :: rest =>
          .next ⟨.expr expression env, .assignAttribute base name rest env :: stack, heap⟩
      | .annAssign (.attribute base _) _ none :: rest =>
          .next ⟨.expr base env, .discard rest env :: stack, heap⟩
      | .annAssign (.name name) _ (some expression) :: rest =>
          .next ⟨.expr expression env, .assign name rest env :: stack, heap⟩
      | .annAssign (.name _) _ none :: rest => .next ⟨.block rest env, stack, heap⟩
      | .assign [.tuple targets] expression :: rest | .assign [.list targets] expression :: rest =>
          match Calls.targetNames targets with
          | some names => .next ⟨.expr expression env, .unpack names rest env :: stack, heap⟩
          | none => .unsupported
      | .augAssign (.name name) op expression :: rest =>
          .next ⟨.expr (.name name) env, .binaryLeft op expression env true :: .assign name rest env :: stack, heap⟩
      | .augAssign (.attribute base name) op expression :: rest =>
          .next ⟨.expr base env, .augmentAttribute name op expression rest env :: stack, heap⟩
      | .assert condition message :: rest =>
          .next ⟨.expr condition env, .assertion message rest env :: stack, heap⟩
      | .ifThen condition yes no :: rest => .next ⟨.expr condition env, .branch yes no rest env :: stack, heap⟩
      | .whileDo condition body otherwise :: rest =>
          .next ⟨.expr condition env,
            .branch (body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)]) otherwise rest env :: stack, heap⟩
      | .forIn (.name name) (.call (.name "range") expressions) body otherwise :: rest =>
          .next (rangeState name env [] expressions body otherwise rest stack heap)
      | .forIn (.name name) iterable body otherwise :: rest =>
          .next ⟨.expr iterable env, .sequence name body otherwise rest env :: stack, heap⟩
      | .forIn (.tuple [.name index, .name name]) (.call (.name "enumerate") [iterable]) body otherwise :: rest
        | .forIn (.list [.name index, .name name]) (.call (.name "enumerate") [iterable]) body otherwise :: rest =>
          .next ⟨.expr iterable env,
            .enumerateSource index name (.constant (.int 0)) body otherwise rest env :: stack, heap⟩
      | .forIn (.tuple [.name index, .name name]) (.call (.name "enumerate") [iterable, start]) body otherwise :: rest
        | .forIn (.list [.name index, .name name]) (.call (.name "enumerate") [iterable, start]) body otherwise :: rest =>
          .next ⟨.expr iterable env, .enumerateSource index name start body otherwise rest env :: stack, heap⟩
      | .enumerateStepLoop index name source position counter body otherwise :: rest =>
          run anchors heap (Mutable.sequence (sequenceValue source)) fun items heap =>
            match items[position]? with
            | none => .next ⟨.block (otherwise ++ rest) env, stack, heap⟩
            | some value => .next ⟨.block (body ++ [Calls.loopContinuation body
                (.enumerateStepLoop index name source (position + 1) (counter + 1) body otherwise)] ++ rest)
                (setLocal (setLocal env index (.scalar (.int counter))) name value), stack, heap⟩
      | .forIn (.tuple targets) iterable body otherwise :: rest
        | .forIn (.list targets) iterable body otherwise :: rest =>
          match Calls.targetNames targets with
          | some names => .next ⟨.expr iterable env, .unpackSequence names body otherwise rest env :: stack, heap⟩
          | none => .unsupported
      | .unpackStepLoop names source position body otherwise :: rest =>
          run anchors heap (Mutable.sequence (sequenceValue source)) fun items heap =>
            match items[position]? with
            | none => .next ⟨.block (otherwise ++ rest) env, stack, heap⟩
            | some value => run anchors heap (Mutable.sequence value) fun fields heap =>
                if names.length = fields.length then
                  .next ⟨.block (body ++ [Calls.loopContinuation body
                    (.unpackStepLoop names source (position + 1) body otherwise)] ++ rest)
                    (assignNames env names fields), stack, heap⟩
                else done anchors heap (.error { typeName := "ValueError", args := [] })
      | .sequenceStepLoop name source position body otherwise :: rest =>
          run anchors heap (Mutable.sequence (sequenceValue source)) fun items heap =>
            match items[position]? with
            | none => .next ⟨.block (otherwise ++ rest) env, stack, heap⟩
            | some value => .next ⟨.block (body ++ [Calls.loopContinuation body
                (.sequenceStepLoop name source (position + 1) body otherwise)] ++ rest)
                (setLocal env name value), stack, heap⟩
      | .rangeStepLoop name next stop stride body otherwise :: rest =>
          if Calls.rangeContinues next stop stride then
            .next ⟨.block (body ++ [Calls.loopContinuation body
              (.rangeStepLoop name (next + stride) stop stride body otherwise)] ++ rest)
              (setLocal env name (.scalar (.int next))), stack, heap⟩
          else .next ⟨.block (otherwise ++ rest) env, stack, heap⟩
      | .loopResume next :: rest => .next ⟨.block (next :: rest) env, stack, heap⟩
      | .breakLoop :: rest => match Calls.loopTarget rest with
          | some (_, following) => .next ⟨.block following env, stack, heap⟩
          | none => .unsupported
      | .continueLoop :: rest => match Calls.loopTarget rest with
          | some (next, following) => .next ⟨.block (next :: following) env, stack, heap⟩
          | none => .unsupported
      | .expr expression :: rest => .next ⟨.expr expression env, .discard rest env :: stack, heap⟩
      | .comprehensionAppend address expression :: rest =>
          .next (argumentsState (.append address) env [] [expression] (.discard rest env :: stack) heap)
      | _ => .unsupported
  | .value value =>
      match stack with
      | [] => done anchors heap (.ok value)
      | frame :: stack => match frame with
          | .sumStart loop env => sumEnter anchors loop env value stack heap
          | .initialized address => match value with
              | .scalar .none => .next ⟨.value (.ref address), stack, heap⟩
              | _ => done anchors heap (.error { typeName := "TypeError", args := [] })
          | .attribute name => result anchors heap (getAttribute module value name) stack
          | .methodReceiver name expressions env =>
              run anchors heap (bindMethod module value name) fun method heap =>
                .next (argumentsState method env [] expressions stack heap)
          | .assignAttribute base name rest env =>
              .next (argumentsState (.setField name value) env [] [base] (.discard rest env :: stack) heap)
          | .augmentAttribute name op right rest env =>
              run anchors heap (getAttribute module value name) fun previous heap =>
                .next ⟨.expr right env, .binaryRight op previous true ::
                  .writeAttribute value name rest env :: stack, heap⟩
          | .writeAttribute receiver name rest env =>
              result anchors heap (Mutable.writeField receiver name value) (.discard rest env :: stack)
          | .comprehensionResult address => .next ⟨.value (.ref address), stack, heap⟩
          | .binaryLeft op right env inPlace => .next ⟨.expr right env, .binaryRight op value inPlace :: stack, heap⟩
          | .binaryRight op left inPlace =>
              result anchors heap (if inPlace then inplace op left value else Mutable.binary op left value) stack
          | .compareLeft op right env => .next ⟨.expr right env, .compareRight op value :: stack, heap⟩
          | .compareRight op left => result anchors heap (compare op left value) stack
          | .chainLeft op right rest env =>
              .next ⟨.expr right env, .chainRight op value rest env :: stack, heap⟩
          | .chainRight op left rest env =>
              result anchors heap (compare op left value) (.chainResult value rest env :: stack)
          | .chainResult right rest env => match rest with
              | [] => .next ⟨.value value, stack, heap⟩
              | (op, next) :: rest => run anchors heap (Mutable.truth value) fun truth heap =>
                  if truth then .next ⟨.expr next env, .chainRight op right rest env :: stack, heap⟩
                  else .next ⟨.value value, stack, heap⟩
          | .unary op => result anchors heap (unary op value) stack
          | .boolean op rest env => run anchors heap (Mutable.truth value) fun truth heap =>
              if (match op with | .and => !truth | .or => truth) then .next ⟨.value value, stack, heap⟩
              else match rest with
                | [] => .next ⟨.value value, stack, heap⟩
                | first :: rest => .next ⟨.expr first env, .boolean op rest env :: stack, heap⟩
          | .conditional yes no env => run anchors heap (Mutable.truth value) fun truth heap =>
              .next ⟨.expr (if truth then yes else no) env, stack, heap⟩
          | .arguments operation done rest env => .next (argumentsState operation env (done ++ [value]) rest stack heap)
          | .addReceiver item env =>
              match value with
              | .ref address => match heap[address]? with
                  | some (.instance _ _ _) => run anchors heap (bindMethod module value "add") fun method heap =>
                      .next (argumentsState method env [] [item] stack heap)
                  | _ => run anchors heap (Mutable.addReceiver value) fun address heap =>
                      .next (argumentsState (.add address) env [] [item] stack heap)
              | .scalar _ => done anchors heap (.error { typeName := "AttributeError", args := [] })
          | .appendReceiver item env => match value with
              | .scalar _ => done anchors heap (.error { typeName := "AttributeError", args := [] })
              | .ref address => match heap[address]? with
                  | some (.instance _ _ _) => run anchors heap (bindMethod module value "append") fun method heap =>
                      .next (argumentsState method env [] [item] stack heap)
                  | _ => run anchors heap (Mutable.appendReceiver value) fun _ heap =>
                      .next (argumentsState (.append address) env [] [item] stack heap)
          | .assignItem base index rest env =>
              .next (argumentsState (.setItem value) env [] [base, index] (.discard rest env :: stack) heap)
          | .assignSlice base lower upper stride rest env =>
              .next (argumentsState (.setSlice value) env [] [base, lower, upper, stride]
                (.discard rest env :: stack) heap)
          | .assign name rest env => .next ⟨.block rest (setLocal env name value), stack, heap⟩
          | .unpack names rest env =>
              run anchors heap (Mutable.sequence value) fun items heap =>
                if names.length = items.length then
                  .next ⟨.block rest (assignNames env names items), stack, heap⟩
                else done anchors heap (.error { typeName := "ValueError", args := [] })
          | .branch yes no rest env => run anchors heap (Mutable.truth value) fun truth heap =>
              .next ⟨.block ((if truth then yes else no) ++ rest) env, stack, heap⟩
          | .assertion message rest env => run anchors heap (Mutable.truth value) fun truth heap =>
              if truth then .next ⟨.block rest env, stack, heap⟩
              else match message with
                | none => done anchors heap (.error { typeName := "AssertionError", args := [] })
                | some expression => .next ⟨.expr expression env, .assertionMessage :: stack, heap⟩
          | .sequence name body otherwise following env =>
              run anchors heap (Mutable.sequence value) fun _ heap =>
                .next ⟨.block (.sequenceStepLoop name (sequenceSource value) 0 body otherwise :: following) env,
                  stack, heap⟩
          | .unpackSequence names body otherwise following env =>
              run anchors heap (Mutable.sequence value) fun _ heap =>
                .next ⟨.block (.unpackStepLoop names (sequenceSource value) 0 body otherwise :: following) env,
                  stack, heap⟩
          | .enumerateSource index name start body otherwise following env =>
              .next ⟨.expr start env, .enumerateStart index name value body otherwise following env :: stack, heap⟩
          | .enumerateStart index name source body otherwise following env =>
              run anchors heap (enumerateStart value) fun counter heap =>
                run anchors heap (Mutable.sequence source) fun _ heap =>
                  .next ⟨.block (.enumerateStepLoop index name (sequenceSource source) 0 counter body otherwise :: following) env,
                    stack, heap⟩
          | .assertionMessage => match value with
              | .scalar value => done anchors heap (.error { typeName := "AssertionError", args := [value] })
              -- Exception arguments currently have a scalar observation boundary.
              | .ref _ => .unsupported
          | .discard rest env => .next ⟨.block rest env, stack, heap⟩
          | .rangeArguments name done rest body otherwise following env =>
              .next (rangeState name env (done ++ [value]) rest body otherwise following stack heap)

/-- Entry references stay observable; freshly allocated unreachable lists do not
become roots in the completion's alias-preserving graph. -/
def call (module : Module) (name : String) (values : List Value) (heap : Heap) : Mutable.Call :=
  ⟨⟨State, ⟨.operation (.call name) values, [], heap⟩, step module heap.length⟩⟩

/-- Preconditions run from the same initial heap as the specified call. Their
private evaluation may allocate or mutate without changing the call's inputs. -/
def evaluate (module : Module) (env : Env) (expression : Expr) (heap : Heap) : Mutable.Call :=
  ⟨⟨State, ⟨.expr expression env, [], heap⟩, step module heap.length⟩⟩

/-- Only Boolean True satisfies a precondition; other truthy values do not. -/
def Condition (module : Module) (env : Env) (expression : Expr) (heap : Heap) : Prop :=
  ∃ finalHeap, (evaluate module env expression heap).Finishes
    ⟨.ok (.scalar (.bool true)), [], finalHeap, heap.length⟩

/-- Scalar entry points can compare with existing scalar interpreters. A list
result is outside this adapter, and must use `call` instead. -/
def scalarStep (module : Module) (state : State) : Step State Constant :=
  match step module 0 state with
  | .next next => .next next
  | .unsupported => .unsupported
  | .done (.ok completion) => match completion.outcome with
      | .ok (.scalar value) => .done (.ok value)
      | .ok (.ref _) => .unsupported
      | .error error => .done (.error error)
  | .done (.error _) => .unsupported

def scalarFunction (module : Module) (name : String) (values : List Constant) : Execution Constant :=
  ⟨State, ⟨.operation (.call name) (values.map Mutable.Value.scalar), [], []⟩, scalarStep module⟩

inductive Reaches (module : Module) (anchors : Nat) : State → State → Prop where
  | refl : Reaches module anchors state state
  | next : step module anchors state = .next following →
      Reaches module anchors following final → Reaches module anchors state final

theorem Reaches.trans (h : Reaches module anchors a b) (rest : Reaches module anchors b c) :
    Reaches module anchors a c := by
  induction h with
  | refl => exact rest
  | next h _ ih => exact .next h (ih rest)

theorem Reaches.finishes (h : Reaches module anchors a b)
    (rest : Finishes (step module anchors) b outcome) : Finishes (step module anchors) a outcome := by
  induction h with
  | refl => exact rest
  | next h _ ih => exact .next h (ih rest)

def Evaluates (module : Module) (env : Env) (expression : Expr)
    (heap : Heap) (value : Value) (finalHeap : Heap) : Prop :=
  ∀ anchors stack, Reaches module anchors ⟨.expr expression env, stack, heap⟩ ⟨.value value, stack, finalHeap⟩

theorem Evaluates.finishes (h : Evaluates module env expression heap value finalHeap) :
    (evaluate module env expression heap).Finishes ⟨.ok value, [], finalHeap, heap.length⟩ :=
  (h heap.length []).finishes (.done rfl)

theorem Evaluates.condition_iff (h : Evaluates module env expression heap value finalHeap) :
    Condition module env expression heap ↔ value = .scalar (.bool true) := by
  constructor
  · rintro ⟨otherHeap, finished⟩
    have same := h.finishes.unique finished
    cases same
    rfl
  · intro same
    subst value
    exact ⟨finalHeap, h.finishes⟩

def ReturnsValue (module : Module) (name : String) (values : List Value)
    (heap : Heap) (value : Value) (finalHeap : Heap) : Prop :=
  ∀ anchors stack, Reaches module anchors ⟨.operation (.call name) values, stack, heap⟩ ⟨.value value, stack, finalHeap⟩

/-- Reuse a helper result when omitted arguments expand to the already proved
argument vector. Both entry steps bind exactly the same local environment. -/
theorem ReturnsValue.with_defaults
    (found : findFunctionIn module.body name = some (args, body))
    (filled : completeArguments args supplied = some values)
    (complete : completeArguments args values = some values)
    (h : ReturnsValue module name values heap value finalHeap) :
    ReturnsValue module name supplied heap value finalHeap := by
  intro anchors stack
  cases h anchors stack with
  | next transition rest =>
      simp only [step, found, complete, Step.next.injEq] at transition
      subst transition
      exact .next (by simp [step, found, filled]) rest

theorem ReturnsValue.finishes (h : ReturnsValue module name values heap value finalHeap) :
    (call module name values heap).Finishes ⟨.ok value, [], finalHeap, heap.length⟩ :=
  (h heap.length []).finishes (.done rfl)

theorem ReturnsValue.returns (h : ReturnsValue module name values heap value finalHeap) :
    (call module name values heap).Returns := ⟨value, [], finalHeap, heap.length, h.finishes⟩

theorem Reaches.scalar_finishes (h : Reaches module 0 a b)
    (rest : Finishes (scalarStep module) b outcome) : Finishes (scalarStep module) a outcome := by
  induction h with
  | refl => exact rest
  | next transition _ ih => exact .next (by simp [scalarStep, transition]) (ih rest)

theorem ReturnsValue.scalar_finishes
    (h : ReturnsValue module name (values.map Mutable.Value.scalar) [] (.scalar value) heap) :
    Finishes (scalarFunction module name values).step (scalarFunction module name values).initial (.ok value) :=
  (h 0 []).scalar_finishes (.done rfl)

theorem ReturnsValue.scalar_returns
    (h : ReturnsValue module name (values.map Mutable.Value.scalar) [] (.scalar value) heap) :
    (scalarFunction module name values).Returns := ⟨value, ReturnsValue.scalar_finishes h⟩

/-- Linking preserves class definitions and their constructor bindings too. -/
structure Extends (target source : Module) : Prop extends Calls.Extends target source where
  classes : ∀ name origin body, source.findClass name = some (origin, body) →
    target.findClass name = some (origin, body) ∧
    findFunctionIn target.body name = findFunctionIn source.body name ∧
    libraryFunction target name = libraryFunction source name

theorem Extends.of_classless (extension : Calls.Extends target source)
    (classless : source.classOrigins = []) : Extends target source := by
  refine ⟨extension, ?_⟩
  intro name origin body found
  simp [Module.findClass, classless] at found

theorem Extends.refl (module : Module) : Extends module module :=
  ⟨Calls.Extends.refl module, fun _ _ _ found => ⟨found, rfl, rfl⟩⟩

theorem Extends.trans (first : Extends middle source) (second : Extends target middle) :
    Extends target source := by
  refine ⟨first.toExtends.trans second.toExtends, ?_⟩
  intro name origin body found
  obtain ⟨middle, functions, libraries⟩ := first.classes name origin body found
  obtain ⟨target, otherFunctions, otherLibraries⟩ := second.classes name origin body middle
  exact ⟨target, otherFunctions.trans functions, otherLibraries.trans libraries⟩

private theorem bindMethod_extend (extension : Extends target source)
    (supported : bindMethod source receiver name heap ≠ none) :
    bindMethod target receiver name heap = bindMethod source receiver name heap := by
  cases receiver with
  | scalar value => rfl
  | ref address =>
      cases found : heap[address]? with
      | none => simp [bindMethod, found]
      | some object =>
          cases object with
          | list items | tuple items | bytearray items | set items => simp [bindMethod, found]
          | «instance» origin className fields =>
              cases defined : source.findClass className with
              | none => simp [bindMethod, found, instanceClass, defined, Mutable.unsupported] at supported
              | some definition =>
                  rcases definition with ⟨identity, body⟩
                  have preserved := (extension.classes className identity body defined).1
                  simp [bindMethod, found, instanceClass, defined, preserved]

private theorem attribute_extend (extension : Extends target source)
    (supported : getAttribute source receiver name heap ≠ none) :
    getAttribute target receiver name heap = getAttribute source receiver name heap := by
  cases receiver with
  | scalar value => rfl
  | ref address =>
      cases found : heap[address]? with
      | none => simp [getAttribute, found]
      | some object =>
          cases object with
          | list items | tuple items | bytearray items | set items =>
              simp [getAttribute, found]
          | «instance» origin className fields =>
              cases defined : source.findClass className with
              | none => simp [getAttribute, found, instanceClass, defined, Mutable.unsupported] at supported
              | some definition =>
                  rcases definition with ⟨identity, body⟩
                  have preserved := (extension.classes className identity body defined).1
                  simp [getAttribute, found, instanceClass, defined, preserved]

private theorem run_extend (left right : Eval α)
    (same : left heap ≠ none → right heap = left heap)
    (supported : run anchors heap left next ≠ .unsupported) :
    run anchors heap right next = run anchors heap left next := by
  have defined : left heap ≠ none := by
    intro missing
    simp [run, missing] at supported
  simp only [run, same defined]

/-- Imported helpers retain their checked bodies and share the caller's heap. -/
theorem step_extend (extension : Extends target source) (state : State)
    (supported : step source anchors state ≠ .unsupported) :
    step target anchors state = step source anchors state := by
  rcases state with ⟨work, stack, heap⟩
  cases work with
  | operation operation values =>
      cases operation with
      | call name =>
          cases found : findFunctionIn source.body name with
          | none =>
              cases imported : libraryFunction source name with
              | none =>
                  cases defined : source.findClass name with
                  | none => simp [step, found, imported, construct, defined] at supported
                  | some definition =>
                      rcases definition with ⟨origin, body⟩
                      obtain ⟨preserved, functions, libraries⟩ := extension.classes name origin body defined
                      simp [step, found, imported, construct, defined, preserved, functions, libraries]
              | some function =>
                  obtain ⟨absent, same⟩ := extension.toExtends.libraryFunction_eq found imported
                  simp only [step, found, absent, library, imported, same]
          | some declaration =>
              rcases declaration with ⟨args, body⟩
              simp only [step, found, extension.functions name args body found]
      | list | tuple | subscript | slice | setItem _ | setSlice _ | append _ | add _ | builtin _ | reversedList | sumSequence | sumGenerator _ _ _ _ | raiseException _ | comprehension _ _ _ | method _ _ _ | notCallable | setField _ _ => rfl
  | expr _ _ | block _ _ | startRange _ _ _ _ _ _ => rfl
  | value value =>
      cases stack with
      | nil => rfl
      | cons frame stack =>
          cases frame with
          | «attribute» name =>
              exact run_extend _ _ (attribute_extend extension) supported
          | methodReceiver name arguments env =>
              exact run_extend _ _ (bindMethod_extend extension) supported
          | augmentAttribute name op right rest env =>
              exact run_extend _ _ (attribute_extend extension) supported
          | addReceiver item env | appendReceiver item env =>
              cases value with
              | scalar _ => rfl
              | ref address =>
                  cases found : heap[address]? with
                  | none => simp [step, found]
                  | some object =>
                      cases object with
                      | list items | tuple items | bytearray items | set items => simp [step, found]
                      | «instance» origin className fields =>
                          simp only [step, found] at supported ⊢
                          exact run_extend _ _ (bindMethod_extend extension) supported
          | _ => rfl

theorem Reaches.extend (h : Reaches source anchors initial final) (extension : Extends target source) :
    Reaches target anchors initial final := by
  induction h with
  | refl => exact .refl
  | next transition _ ih =>
      apply Reaches.next _ ih
      rw [step_extend extension _ (by simp [transition])]
      exact transition

theorem ReturnsValue.extend (h : ReturnsValue source name values heap value finalHeap)
    (extension : Extends target source) : ReturnsValue target name values heap value finalHeap :=
  fun anchors stack => (h anchors stack).extend extension


namespace Evaluates

theorem constant : Evaluates module env (.constant value) heap (.scalar value) heap :=
  fun _ _ => .next rfl .refl

theorem lookup (h : env name = some value) : Evaluates module env (.name name) heap value heap :=
  fun _ _ => .next (by simp [step, h]) .refl

theorem binary (left : Evaluates module env a heap av middle)
    (right : Evaluates module env b middle bv afterRight)
    (operation : Mutable.binary op av bv afterRight = some (.ok value, finalHeap)) :
    Evaluates module env (.binOp a op b) heap value finalHeap := by
  intro anchors stack
  exact .next rfl ((left _ _).trans (.next rfl ((right _ _).trans
    (.next (by simp [step, result, run, operation]) .refl))))

theorem unary (evaluated : Evaluates module env expression heap value middle)
    (operation : HeapCalls.unary op value middle = some (.ok resultValue, finalHeap)) :
    Evaluates module env (.unaryOp op expression) heap resultValue finalHeap := by
  intro anchors stack
  exact .next rfl ((evaluated anchors _).trans
    (.next (by simp [step, result, run, operation]) .refl))

theorem compare (left : Evaluates module env a heap av middle)
    (right : Evaluates module env b middle bv afterRight)
    (operation : HeapCalls.compare op av bv afterRight = some (.ok value, finalHeap)) :
    Evaluates module env (.compare a [(op, b)]) heap value finalHeap := by
  intro anchors stack
  exact .next rfl ((left _ _).trans (.next rfl ((right _ _).trans
    (.next (by simp [step, result, run, operation]) .refl))))

/-- Continue a comparison chain with the middle operand's value already evaluated. -/
def Compares (module : Module) (env : Env) (left : Value) (op : CmpOp) (right : Expr)
    (rest : List (CmpOp × Expr)) (heap : Heap) (answer : Value) (finalHeap : Heap) : Prop :=
  ∀ anchors stack,
    Reaches module anchors ⟨.expr right env, .chainRight op left rest env :: stack, heap⟩
      ⟨.value answer, stack, finalHeap⟩

namespace Compares

theorem last (evaluated : Evaluates module env right heap value middle)
    (operation : HeapCalls.compare op left value middle = some (.ok answer, finalHeap)) :
    Compares module env left op right [] heap answer finalHeap := by
  intro anchors stack
  apply (evaluated anchors _).trans
  apply Reaches.next (following :=
    ⟨.value answer, .chainResult value [] env :: stack, finalHeap⟩)
    (by simp [step, result, run, operation])
  exact .next rfl .refl

theorem stop (evaluated : Evaluates module env right heap value middle)
    (operation : HeapCalls.compare op left value middle = some (.ok answer, finalHeap))
    (truth : Mutable.truth answer finalHeap = some (.ok false, finalHeap)) :
    Compares module env left op right (next :: rest) heap answer finalHeap := by
  intro anchors stack
  apply (evaluated anchors _).trans
  apply Reaches.next (following :=
    ⟨.value answer, .chainResult value (next :: rest) env :: stack, finalHeap⟩)
    (by simp [step, result, run, operation])
  cases next
  exact .next (by simp [step, run, truth]) .refl

theorem next (evaluated : Evaluates module env right heap value middle)
    (operation : HeapCalls.compare op left value middle = some (.ok compared, afterComparison))
    (truth : Mutable.truth compared afterComparison = some (.ok true, afterComparison))
    (following : Compares module env value nextOp nextRight rest afterComparison answer finalHeap) :
    Compares module env left op right ((nextOp, nextRight) :: rest) heap answer finalHeap := by
  intro anchors stack
  apply (evaluated anchors _).trans
  apply Reaches.next (following :=
    ⟨.value compared, .chainResult value ((nextOp, nextRight) :: rest) env :: stack,
      afterComparison⟩) (by simp [step, result, run, operation])
  exact .next (by simp [step, run, truth]) (following anchors stack)

end Compares

theorem chain (left : Evaluates module env expression heap value middle)
    (following : Compares module env value op right (next :: rest) middle answer finalHeap) :
    Evaluates module env (.compare expression ((op, right) :: next :: rest)) heap answer finalHeap := by
  intro anchors stack
  exact .next rfl ((left anchors _).trans (.next rfl (following anchors stack)))

/-- Short-circuiting returns the first operand without evaluating later expressions. -/
theorem boolean_stop (evaluated : Evaluates module env first heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (stop : (match op with | .and => !flag | .or => flag) = true) :
    Evaluates module env (.boolOp op (first :: rest)) heap value middle := by
  intro anchors stack
  exact .next rfl ((evaluated anchors _).trans
    (.next (by simp [step, run, truth, stop]) .refl))

/-- The last operand supplies the result, preserving its value and heap effects. -/
theorem boolean_last (evaluated : Evaluates module env expression heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle)) :
    Evaluates module env (.boolOp op [expression]) heap value middle := by
  intro anchors stack
  apply Reaches.next rfl
  apply (evaluated anchors _).trans
  apply Reaches.next _ .refl
  cases op <;> cases flag <;> simp [step, run, truth]

/-- A non-short-circuiting operand continues in the heap it produced. -/
theorem boolean_next (evaluated : Evaluates module env first heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (continues : (match op with | .and => !flag | .or => flag) = false)
    (rest : Evaluates module env (.boolOp op (next :: tail)) middle answer finalHeap) :
    Evaluates module env (.boolOp op (first :: next :: tail)) heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (evaluated anchors _).trans
  cases rest anchors stack with
  | next transition following =>
      simp only [step, Step.next.injEq] at transition
      subst transition
      exact .next (by simp [step, run, truth, continues]) following

theorem conditional (condition : Evaluates module env test heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (branch : Evaluates module env (if flag then yes else no) middle answer finalHeap) :
    Evaluates module env (.ifExp test yes no) heap answer finalHeap := by
  intro anchors stack
  exact .next rfl ((condition anchors _).trans
    (.next (by simp [step, run, truth]) (branch anchors stack)))

inductive Arguments (module : Module) (env : Env) : List Expr → Heap → List Value → Heap → Prop where
  | nil : Arguments module env [] heap [] heap
  | cons : Evaluates module env expression heap value middle →
      Arguments module env expressions middle values finalHeap →
      Arguments module env (expression :: expressions) heap (value :: values) finalHeap

/-- Argument expressions retain left-to-right effects for every call operation. -/
theorem arguments_reach (h : Arguments module env expressions heap values finalHeap)
    (operation : Operation) (done : List Value) (anchors : Nat) (stack : List Frame) :
    Reaches module anchors (argumentsState operation env done expressions stack heap)
      ⟨.operation operation (done ++ values), stack, finalHeap⟩ := by
  induction h generalizing done with
  | nil => simp [argumentsState]; exact .refl
  | @cons expression heap value middle expressions values finalHeap head tail ih =>
      apply (head _ _).trans
      refine .next rfl ?_
      simpa [List.append_assoc] using ih (done ++ [value])

theorem call (arguments : Arguments module env expressions heap values middle)
    (callee : ReturnsValue module name values middle value finalHeap) :
    Evaluates module env (.call (.name name) expressions) heap value finalHeap := by
  intro anchors stack
  exact .next rfl ((arguments_reach arguments (.call name) [] anchors stack).trans (callee anchors stack))

theorem library_call (arguments : Arguments module env expressions heap values middle)
    (absent : findFunctionIn module.body name = none)
    (operation : library module name values middle = some (.ok value, finalHeap)) :
    Evaluates module env (.call (.name name) expressions) heap value finalHeap := by
  cases imported : libraryFunction module name with
  | none => simp [library, imported, Mutable.unsupported] at operation
  | some implementation =>
      apply call arguments
      intro anchors stack
      exact .next (by simp [step, absent, imported, result, run, operation]) .refl

theorem qualified_call (notAppend : field ≠ "append")
    (arguments : Arguments module env expressions heap values middle)
    (callee : ReturnsValue module (alias ++ "." ++ field) values middle value finalHeap)
    (notAdd : field ≠ "add" := by decide)
    (unbound : env alias = none := by rfl) :
    Evaluates module env (.call (.attribute (.name alias) field) expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := argumentsState (.call (alias ++ "." ++ field)) env [] expressions stack heap)
    (by simp [step, notAppend, notAdd, unbound])
  exact (arguments_reach arguments (.call (alias ++ "." ++ field)) [] anchors stack).trans (callee anchors stack)

theorem list (arguments : Arguments module env expressions heap values finalHeap) :
    Evaluates module env (.list expressions) heap (.ref finalHeap.length) (finalHeap ++ [.list values]) := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments .list [] anchors stack).trans
  exact .next (by simp [step, result, run, primitive, Mutable.allocate, Except.map]) .refl

/-- Nonempty runtime tuple displays allocate after all their elements evaluate. -/
theorem tuple (arguments : Arguments module env expressions heap values finalHeap)
    (nonempty : values ≠ []) :
    Evaluates module env (.tuple expressions) heap (.ref finalHeap.length)
      (finalHeap ++ [.tuple values]) := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments .tuple [] anchors stack).trans
  exact .next (by simp [step, result, run, primitive, Mutable.allocateTuple, nonempty, Except.map]) .refl

/-- Subscription evaluates its receiver and index before reading the shared heap. -/
theorem subscript
    (ordinary : ∀ a b c, index ≠ .slice a b c)
    (receiver : Evaluates module env base heap value middle)
    (subscript : Evaluates module env index middle position afterIndex)
    (operation : Mutable.getItem value position afterIndex = some (.ok answer, finalHeap)) :
    Evaluates module env (.subscript base index) heap answer finalHeap := by
  intro anchors stack
  have start : step module anchors ⟨.expr (.subscript base index) env, stack, heap⟩ =
      .next ⟨.expr base env, .arguments .subscript [] [index] env :: stack, heap⟩ := by
    cases index <;> simp_all [step, argumentsState]
  apply Reaches.next start
  apply (receiver anchors _).trans
  apply Reaches.next rfl
  apply (subscript anchors _).trans
  apply Reaches.next rfl
  exact .next (by simp [argumentsState, step, primitive, result, run, operation]) .refl

/-- Slice arguments evaluate left to right, retaining effects before allocation. -/
theorem slice (arguments : Arguments module env
    [base, lower.getD (.constant .none), upper.getD (.constant .none), stride.getD (.constant .none)]
    heap [receiver, first, last, stepValue] middle)
    (operation : Mutable.getSlice receiver first last stepValue middle = some (.ok value, finalHeap)) :
    Evaluates module env (.subscript base (.slice lower upper stride)) heap value finalHeap := by
  intro anchors stack
  exact .next rfl ((arguments_reach arguments .slice [] anchors stack).trans
    (.next (by simp [step, primitive, result, run, operation]) .refl))

theorem reversed_list (evaluated : Evaluates module env expression heap (.ref address) middle)
    (found : middle[address]? = some (.list items)) :
    Evaluates module env (.reversedList expression) heap (.ref middle.length)
      (middle ++ [.list items.reverse]) := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach (.cons evaluated .nil) .reversedList [] anchors stack).trans
  exact .next (by simp [step, result, run, primitive, Mutable.sequence, found,
    Mutable.allocate, Except.map]) .refl

theorem builtin (arguments : Arguments module env expressions heap values middle)
    (operation : primitive (.builtin name) values middle = some (.ok value, finalHeap)) :
    Evaluates module env (.builtinCall name expressions) heap value finalHeap := by
  intro anchors stack
  exact .next rfl ((arguments_reach arguments (.builtin name) [] anchors stack).trans
    (.next (by simp [step, result, run, operation]) .refl))

theorem append (receiver : Evaluates module env base heap (.ref address) middle)
    (found : middle[address]? = some (.list old))
    (item : Evaluates module env expression middle value afterItem)
    (items : afterItem[address]? = some (.list current)) :
    Evaluates module env (.call (.attribute base "append") [expression]) heap (.scalar .none)
      (afterItem.set address (.list (current ++ [value]))) := by
  intro anchors stack
  apply Reaches.next rfl
  apply (receiver anchors _).trans
  apply Reaches.next (following := ⟨.expr expression env,
    .arguments (.append address) [] [] env :: stack, middle⟩)
    (by simp [step, run, Mutable.appendReceiver, found, argumentsState])
  apply (item anchors _).trans
  apply Reaches.next (following := ⟨.operation (.append address) [value], stack, afterItem⟩) rfl
  exact .next (by simp [step, result, run, primitive, Mutable.appendItem, items, Except.map]) .refl

/-- Method lookup precedes argument evaluation, which may itself mutate the set. -/
theorem add (receiver : Evaluates module env base heap (.ref address) middle)
    (found : middle[address]? = some (.set old))
    (item : Evaluates module env expression middle (.scalar value) afterItem)
    (items : afterItem[address]? = some (.set current)) :
    Evaluates module env (.call (.attribute base "add") [expression]) heap (.scalar .none)
      (afterItem.set address (.set (ScalarSet.insert current value))) := by
  intro anchors stack
  apply Reaches.next rfl
  apply (receiver anchors _).trans
  apply Reaches.next (following := ⟨.expr expression env,
    .arguments (.add address) [] [] env :: stack, middle⟩)
    (by simp [step, run, Mutable.addReceiver, found, argumentsState])
  apply (item anchors _).trans
  apply Reaches.next (following := ⟨.operation (.add address) [.scalar value], stack, afterItem⟩) rfl
  exact .next (by simp [step, result, run, primitive, Mutable.addItem, items, Except.map]) .refl

end Evaluates

def BlockReturns (module : Module) (env : Env) (body : List Stmt)
    (heap : Heap) (value : Value) (finalHeap : Heap) : Prop :=
  ∀ anchors stack, Reaches module anchors ⟨.block body env, stack, heap⟩ ⟨.value value, stack, finalHeap⟩

namespace BlockReturns

theorem return_value (evaluated : Evaluates module env expression heap value finalHeap) :
    BlockReturns module env (.return expression :: rest) heap value finalHeap :=
  fun anchors stack => .next rfl (evaluated anchors stack)

theorem assign (evaluated : Evaluates module env expression heap value middle)
    (rest : BlockReturns module (setLocal env name value) body middle answer finalHeap) :
    BlockReturns module env (.assign [.name name] expression :: body) heap answer finalHeap :=
  fun anchors stack => .next rfl ((evaluated anchors _).trans (.next rfl (rest anchors stack)))

theorem unpack (targets : Calls.targetNames expressions = some names)
    (evaluated : Evaluates module env expression heap value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, afterUnpack))
    (arity : names.length = items.length)
    (rest : BlockReturns module (assignNames env names items) body afterUnpack answer finalHeap) :
    BlockReturns module env (.assign [.tuple expressions] expression :: body) heap answer finalHeap := by
  intro anchors stack
  exact .next (following := ⟨.expr expression env, .unpack names body env :: stack, heap⟩)
    (by simp [step, targets]) ((evaluated anchors _).trans
    (.next (by simp [step, run, sequence, arity]) (rest anchors stack)))

/-- Subscription assignment evaluates the RHS before the receiver and index. -/
theorem setItem
    (ordinary : ∀ a b c, index ≠ .slice a b c)
    (rhs : Evaluates module env expression heap value afterRhs)
    (target : Evaluates.Arguments module env [base, index] afterRhs [receiver, subscript] afterTarget)
    (write : Mutable.setItem receiver subscript value afterTarget = some (.ok (.scalar .none), afterWrite))
    (rest : BlockReturns module env body afterWrite answer finalHeap) :
    BlockReturns module env (.assign [.subscript base index] expression :: body) heap answer finalHeap := by
  intro anchors stack
  have start : step module anchors ⟨.block (.assign [.subscript base index] expression :: body) env, stack, heap⟩ =
      .next ⟨.expr expression env, .assignItem base index body env :: stack, heap⟩ := by
    cases index <;> simp_all [step]
  apply Reaches.next start
  apply (rhs anchors _).trans
  apply Reaches.next rfl
  apply (Evaluates.arguments_reach target (.setItem value) [] anchors _).trans
  exact .next (following := ⟨.value (.scalar .none), .discard body env :: stack, afterWrite⟩)
    (by simp [step, result, run, primitive, write]) (.next rfl (rest anchors stack))

/-- Slice bounds run left to right after the RHS and receiver; conversion follows. -/
theorem setSlice
    (rhs : Evaluates module env expression heap value afterRhs)
    (target : Evaluates.Arguments module env [base, lower.getD (.constant .none),
      upper.getD (.constant .none), stride.getD (.constant .none)] afterRhs
      [receiver, lowerValue, upperValue, strideValue] afterTarget)
    (write : Mutable.setSlice receiver lowerValue upperValue strideValue value afterTarget =
      some (.ok (.scalar .none), afterWrite))
    (rest : BlockReturns module env body afterWrite answer finalHeap) :
    BlockReturns module env (.assign [.subscript base (.slice lower upper stride)] expression :: body)
      heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (rhs anchors _).trans
  apply Reaches.next rfl
  apply (Evaluates.arguments_reach target (.setSlice value) [] anchors _).trans
  exact .next (following := ⟨.value (.scalar .none), .discard body env :: stack, afterWrite⟩)
    (by simp [step, result, run, primitive, write]) (.next rfl (rest anchors stack))

theorem augAssign (lookup : env name = some left)
    (evaluated : Evaluates module env expression heap right middle)
    (operation : inplace op left right middle = some (.ok value, afterOperation))
    (rest : BlockReturns module (setLocal env name value) body afterOperation answer finalHeap) :
    BlockReturns module env (.augAssign (.name name) op expression :: body) heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (Evaluates.lookup (module := module) (heap := heap) lookup anchors _).trans
  apply Reaches.next rfl
  apply (evaluated anchors _).trans
  exact .next (following := ⟨.value value, .assign name body env :: stack, afterOperation⟩)
    (by simp [step, result, run, operation]) (.next rfl (rest anchors stack))

theorem discard (evaluated : Evaluates module env expression heap value middle)
    (rest : BlockReturns module env body middle answer finalHeap) :
    BlockReturns module env (.expr expression :: body) heap answer finalHeap :=
  fun anchors stack => .next rfl ((evaluated anchors _).trans (.next rfl (rest anchors stack)))

/-- Successful assertions retain condition effects and skip the message. -/
theorem assertion (evaluated : Evaluates module env condition heap value middle)
    (truth : Mutable.truth value middle = some (.ok true, middle))
    (rest : BlockReturns module env body middle answer finalHeap) :
    BlockReturns module env (.assert condition message :: body) heap answer finalHeap := by
  intro anchors stack
  exact .next rfl ((evaluated anchors _).trans
    (.next (by simp [step, run, truth]) (rest anchors stack)))

theorem branch (evaluated : Evaluates module env condition heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockReturns module env ((if flag then yes else no) ++ body) middle answer finalHeap) :
    BlockReturns module env (.ifThen condition yes no :: body) heap answer finalHeap := by
  intro anchors stack
  exact .next rfl ((evaluated anchors _).trans (.next (by simp [step, run, truth]) (rest anchors stack)))

theorem while_loop (evaluated : Evaluates module env condition heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockReturns module env
      ((if flag then body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)] else otherwise) ++ following)
      middle answer finalHeap) :
    BlockReturns module env (.whileDo condition body otherwise :: following) heap answer finalHeap := by
  intro anchors stack
  exact .next rfl ((evaluated anchors _).trans (.next (by simp [step, run, truth]) (rest anchors stack)))

private theorem range_reach
    (h : Evaluates.Arguments module env expressions heap values finalHeap) (done : List Value)
    (anchors : Nat) (stack : List Frame) :
    Reaches module anchors (rangeState name env done expressions body otherwise following stack heap)
      ⟨.startRange name (done ++ values) body otherwise following env, stack, finalHeap⟩ := by
  induction h generalizing done with
  | nil => simp [rangeState]; exact .refl
  | @cons expression heap value middle expressions values finalHeap head tail ih =>
      apply (head _ _).trans
      refine .next rfl ?_
      simpa [List.append_assoc] using ih (done ++ [value])

theorem for_range (arguments : Evaluates.Arguments module env expressions heap values middle)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (rest : BlockReturns module env (.rangeStepLoop name start stop stride body otherwise :: following)
      middle answer finalHeap) :
    BlockReturns module env (.forIn (.name name) (.call (.name "range") expressions) body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  exact .next rfl ((range_reach arguments [] anchors stack).trans
    (.next (by simp [step, bounds]) (rest anchors stack)))

/-- Evaluate a sequence expression once, then retain its object identity. -/
theorem for_sequence (ordinary : ∀ expressions, iterable ≠ .call (.name "range") expressions)
    (evaluated : Evaluates module env iterable heap value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, middle))
    (rest : BlockReturns module env
      (.sequenceStepLoop name (sequenceSource value) 0 body otherwise :: following) middle answer finalHeap) :
    BlockReturns module env (.forIn (.name name) iterable body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  have start : step module anchors ⟨.block (.forIn (.name name) iterable body otherwise :: following) env, stack, heap⟩ =
      .next ⟨.expr iterable env, .sequence name body otherwise following env :: stack, heap⟩ := by
    cases iterable <;> simp_all [step]
  exact .next start ((evaluated anchors _).trans
    (.next (by simp [step, run, sequence]) (rest anchors stack)))

/-- Iteration reads the current sequence, so mutations in earlier iterations remain visible. -/
theorem sequence_step (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (rest : BlockReturns module (setLocal env name value)
      (body ++ [Calls.loopContinuation body (.sequenceStepLoop name source (position + 1) body otherwise)] ++ following)
      heap answer finalHeap) :
    BlockReturns module env (.sequenceStepLoop name source position body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, run, sequence, item]) (rest anchors stack)

theorem sequence_done (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (finished : items[position]? = none)
    (rest : BlockReturns module env (otherwise ++ following) heap answer finalHeap) :
    BlockReturns module env (.sequenceStepLoop name source position body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, run, sequence, finished]) (rest anchors stack)

theorem range_step (continues : Calls.rangeContinues next stop stride = true)
    (rest : BlockReturns module (setLocal env name (.scalar (.int next)))
      (body ++ [Calls.loopContinuation body (.rangeStepLoop name (next + stride) stop stride body otherwise)] ++ following)
      heap answer finalHeap) :
    BlockReturns module env (.rangeStepLoop name next stop stride body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, continues]) (rest anchors stack)

theorem range_done (finished : Calls.rangeContinues next stop stride = false)
    (rest : BlockReturns module env (otherwise ++ following) heap answer finalHeap) :
    BlockReturns module env (.rangeStepLoop name next stop stride body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, finished]) (rest anchors stack)

theorem loop_resume (rest : BlockReturns module env (next :: following) heap answer finalHeap) :
    BlockReturns module env (.loopResume next :: following) heap answer finalHeap :=
  fun anchors stack => .next rfl (rest anchors stack)

theorem break_loop (target : Calls.loopTarget body = some (next, following))
    (rest : BlockReturns module env following heap answer finalHeap) :
    BlockReturns module env (.breakLoop :: body) heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, target]) (rest anchors stack)

theorem continue_loop (target : Calls.loopTarget body = some (next, following))
    (rest : BlockReturns module env (next :: following) heap answer finalHeap) :
    BlockReturns module env (.continueLoop :: body) heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, target]) (rest anchors stack)

theorem function (found : findFunctionIn module.body name = some (args, body))
    (arguments : completeArguments args values = some completed)
    (evaluated : BlockReturns module (argumentEnv args completed) (executableBody body) heap value finalHeap) :
    ReturnsValue module name values heap value finalHeap := by
  intro anchors stack
  exact .next (by simp [step, found, arguments]) (evaluated anchors stack)

end BlockReturns

/-- Normal completion of a statement block, preserving any following statements
and caller continuation while exposing the updated locals and shared heap. -/
def BlockContinues (module : Module) (env : Env) (body : List Stmt)
    (heap : Heap) (finalEnv : Env) (finalHeap : Heap) : Prop :=
  ∀ following anchors stack,
    Reaches module anchors ⟨.block (body ++ following) env, stack, heap⟩
      ⟨.block following finalEnv, stack, finalHeap⟩

namespace BlockContinues

theorem nil : BlockContinues module env [] heap env heap :=
  fun _ _ _ => .refl

theorem append (first : BlockContinues module env body heap middleEnv middleHeap)
    (second : BlockContinues module middleEnv rest middleHeap finalEnv finalHeap) :
    BlockContinues module env (body ++ rest) heap finalEnv finalHeap := by
  intro following anchors stack
  simpa only [List.append_assoc] using
    (first (rest ++ following) anchors stack).trans (second following anchors stack)

theorem assign (evaluated : Evaluates module env expression heap value finalHeap) :
    BlockContinues module env [.assign [.name name] expression] heap
      (setLocal env name value) finalHeap :=
  fun _ anchors _ => .next rfl ((evaluated anchors _).trans (.next rfl .refl))

theorem annAssign (evaluated : Evaluates module env expression heap value finalHeap) :
    BlockContinues module env [.annAssign (.name name) annotation (some expression)] heap
      (setLocal env name value) finalHeap :=
  fun _ anchors _ => .next rfl ((evaluated anchors _).trans (.next rfl .refl))

theorem annotation (annotation : Expr) : BlockContinues module env [.annAssign (.name name) annotation none] heap env heap :=
  fun _ _ _ => .next rfl .refl

theorem unpack (targets : Calls.targetNames expressions = some names)
    (evaluated : Evaluates module env expression heap value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, finalHeap))
    (arity : names.length = items.length) :
    BlockContinues module env [.assign [.tuple expressions] expression] heap
      (assignNames env names items) finalHeap := by
  intro following anchors stack
  exact .next (following := ⟨.expr expression env, .unpack names following env :: stack, heap⟩)
    (by simp [step, targets]) ((evaluated anchors _).trans
    (.next (by simp [step, run, sequence, arity]) .refl))

/-- Augmented assignment exposes its updated local and heap to following statements. -/
theorem augAssign (lookup : env name = some left)
    (evaluated : Evaluates module env expression heap right middle)
    (operation : inplace op left right middle = some (.ok value, finalHeap)) :
    BlockContinues module env [.augAssign (.name name) op expression] heap
      (setLocal env name value) finalHeap := by
  intro following anchors stack
  apply Reaches.next rfl
  apply (Evaluates.lookup (module := module) (heap := heap) lookup anchors _).trans
  apply Reaches.next rfl
  apply (evaluated anchors _).trans
  exact .next (following := ⟨.value value, .assign name following env :: stack, finalHeap⟩)
    (by simp [step, result, run, operation]) (.next rfl .refl)

/-- Subscription assignment evaluates the RHS before the receiver and index. -/
theorem setItem
    (ordinary : ∀ a b c, index ≠ .slice a b c)
    (rhs : Evaluates module env expression heap value afterRhs)
    (target : Evaluates.Arguments module env [base, index] afterRhs [receiver, subscript] afterTarget)
    (write : Mutable.setItem receiver subscript value afterTarget = some (.ok (.scalar .none), afterWrite)) :
    BlockContinues module env [.assign [.subscript base index] expression] heap env afterWrite := by
  intro body anchors stack
  have start : step module anchors ⟨.block (.assign [.subscript base index] expression :: body) env, stack, heap⟩ =
      .next ⟨.expr expression env, .assignItem base index body env :: stack, heap⟩ := by
    cases index <;> simp_all [step]
  apply Reaches.next start
  apply (rhs anchors _).trans
  apply Reaches.next rfl
  apply (Evaluates.arguments_reach target (.setItem value) [] anchors _).trans
  exact .next (following := ⟨.value (.scalar .none), .discard body env :: stack, afterWrite⟩)
    (by simp [step, result, run, primitive, write]) (.next rfl .refl)

/-- Slice bounds run left to right after the RHS and receiver; conversion follows. -/
theorem setSlice
    (rhs : Evaluates module env expression heap value afterRhs)
    (target : Evaluates.Arguments module env [base, lower.getD (.constant .none),
      upper.getD (.constant .none), stride.getD (.constant .none)] afterRhs
      [receiver, lowerValue, upperValue, strideValue] afterTarget)
    (write : Mutable.setSlice receiver lowerValue upperValue strideValue value afterTarget =
      some (.ok (.scalar .none), afterWrite)) :
    BlockContinues module env [.assign [.subscript base (.slice lower upper stride)] expression]
      heap env afterWrite := by
  intro body anchors stack
  apply Reaches.next rfl
  apply (rhs anchors _).trans
  apply Reaches.next rfl
  apply (Evaluates.arguments_reach target (.setSlice value) [] anchors _).trans
  exact .next (following := ⟨.value (.scalar .none), .discard body env :: stack, afterWrite⟩)
    (by simp [step, result, run, primitive, write]) (.next rfl .refl)

theorem discard (evaluated : Evaluates module env expression heap value finalHeap) :
    BlockContinues module env [.expr expression] heap env finalHeap :=
  fun _ anchors _ => .next rfl ((evaluated anchors _).trans (.next rfl .refl))

theorem branch (evaluated : Evaluates module env condition heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (body : BlockContinues module env (if flag then yes else no) middle finalEnv finalHeap) :
    BlockContinues module env [.ifThen condition yes no] heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next rfl ((evaluated anchors _).trans
    (.next (by simp [step, run, truth]) (body following anchors stack)))

/-- A while loop exposes its final locals and heap to the following block. -/
theorem while_loop (evaluated : Evaluates module env condition heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockContinues module env
      (if flag then body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)] else otherwise)
      middle finalEnv finalHeap) :
    BlockContinues module env [.whileDo condition body otherwise] heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next rfl ((evaluated anchors _).trans
    (.next (by simp [step, run, truth]) (rest following anchors stack)))

theorem for_range (arguments : Evaluates.Arguments module env expressions heap values middle)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (executed : BlockContinues module env [.rangeStepLoop name start stop stride body otherwise]
      middle finalEnv finalHeap) :
    BlockContinues module env [.forIn (.name name) (.call (.name "range") expressions) body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next rfl ((BlockReturns.range_reach arguments [] anchors stack).trans
    (.next (by simp [step, bounds]) (executed following anchors stack)))

theorem for_sequence (ordinary : ∀ expressions, iterable ≠ .call (.name "range") expressions)
    (evaluated : Evaluates module env iterable heap value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, middle))
    (rest : BlockContinues module env
      [.sequenceStepLoop name (sequenceSource value) 0 body otherwise] middle finalEnv finalHeap) :
    BlockContinues module env [.forIn (.name name) iterable body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  have start : step module anchors ⟨.block (.forIn (.name name) iterable body otherwise :: following) env, stack, heap⟩ =
      .next ⟨.expr iterable env, .sequence name body otherwise following env :: stack, heap⟩ := by
    cases iterable <;> simp_all [step]
  exact .next start ((evaluated anchors _).trans
    (.next (by simp [step, run, sequence]) (rest following anchors stack)))

theorem sequence_step (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (rest : BlockContinues module (setLocal env name value)
      (body ++ [Calls.loopContinuation body (.sequenceStepLoop name source (position + 1) body otherwise)])
      heap finalEnv finalHeap) :
    BlockContinues module env [.sequenceStepLoop name source position body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  refine .next ?_ (rest following anchors stack)
  simp [step, run, sequence, item, List.append_assoc]

theorem sequence_done (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (finished : items[position]? = none)
    (rest : BlockContinues module env otherwise heap finalEnv finalHeap) :
    BlockContinues module env [.sequenceStepLoop name source position body otherwise]
      heap finalEnv finalHeap :=
  fun following anchors stack => .next (by simp [step, run, sequence, finished]) (rest following anchors stack)

/-- The outer sequence is evaluated once; each item is unpacked just before its body. -/
theorem for_unpack
    (ordinary : ∀ expressions, iterable ≠ .call (.name "enumerate") expressions)
    (targets : Calls.targetNames expressions = some names)
    (evaluated : Evaluates module env iterable heap value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, middle))
    (rest : BlockContinues module env
      [.unpackStepLoop names (sequenceSource value) 0 body otherwise] middle finalEnv finalHeap) :
    BlockContinues module env [.forIn (.tuple expressions) iterable body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  have start : step module anchors
      ⟨.block (.forIn (.tuple expressions) iterable body otherwise :: following) env, stack, heap⟩ =
      .next ⟨.expr iterable env, .unpackSequence names body otherwise following env :: stack, heap⟩ := by
    cases iterable <;> simp_all [step]
  exact .next start ((evaluated anchors _).trans
    (.next (by simp [step, run, sequence]) (rest following anchors stack)))

/-- Validate the entire item before assigning names left to right, preserving aliases. -/
theorem unpack_step
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (fields : Mutable.sequence value heap = some (.ok values, heap))
    (arity : names.length = values.length)
    (rest : BlockContinues module (assignNames env names values)
      (body ++ [Calls.loopContinuation body (.unpackStepLoop names source (position + 1) body otherwise)])
      heap finalEnv finalHeap) :
    BlockContinues module env [.unpackStepLoop names source position body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  refine .next ?_ (rest following anchors stack)
  simp [step, run, sequence, item, fields, arity, List.append_assoc]

theorem unpack_done
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (finished : items[position]? = none)
    (rest : BlockContinues module env otherwise heap finalEnv finalHeap) :
    BlockContinues module env [.unpackStepLoop names source position body otherwise]
      heap finalEnv finalHeap :=
  fun following anchors stack => .next (by simp [step, run, sequence, finished]) (rest following anchors stack)

/-- Evaluate the iterable and explicit start before constructing the iterator. -/
theorem for_enumerate_start
    (iterable : Evaluates module env expression heap source afterSource)
    (start : Evaluates module env startExpression afterSource startValue middle)
    (counter : enumerateStart startValue middle = some (.ok initial, middle))
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (rest : BlockContinues module env
      [.enumerateStepLoop index name (sequenceSource source) 0 initial body otherwise] middle finalEnv finalHeap) :
    BlockContinues module env
      [.forIn (.tuple [.name index, .name name]) (.call (.name "enumerate") [expression, startExpression]) body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next rfl ((iterable anchors _).trans (.next rfl ((start anchors _).trans
    (.next (by simp [step, run, counter, sequence]) (rest following anchors stack)))))

theorem for_enumerate
    (iterable : Evaluates module env expression heap source middle)
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (rest : BlockContinues module env
      [.enumerateStepLoop index name (sequenceSource source) 0 0 body otherwise] middle finalEnv finalHeap) :
    BlockContinues module env
      [.forIn (.tuple [.name index, .name name]) (.call (.name "enumerate") [expression]) body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next rfl ((iterable anchors _).trans (.next rfl (.next rfl
    (.next (by simp [step, run, enumerateStart, sequence]) (rest following anchors stack)))))

/-- The hidden pair cannot escape immediate unpacking; its two bindings are ordered. -/
theorem enumerate_step
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (rest : BlockContinues module (setLocal (setLocal env index (.scalar (.int counter))) name value)
      (body ++ [Calls.loopContinuation body
        (.enumerateStepLoop index name source (position + 1) (counter + 1) body otherwise)])
      heap finalEnv finalHeap) :
    BlockContinues module env [.enumerateStepLoop index name source position counter body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  refine .next ?_ (rest following anchors stack)
  simp [step, run, sequence, item, List.append_assoc]

theorem enumerate_done
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (finished : items[position]? = none)
    (rest : BlockContinues module env otherwise heap finalEnv finalHeap) :
    BlockContinues module env [.enumerateStepLoop index name source position counter body otherwise]
      heap finalEnv finalHeap :=
  fun following anchors stack => .next (by simp [step, run, sequence, finished]) (rest following anchors stack)

theorem range_step (continues : Calls.rangeContinues next stop stride = true)
    (rest : BlockContinues module (setLocal env name (.scalar (.int next)))
      (body ++ [Calls.loopContinuation body (.rangeStepLoop name (next + stride) stop stride body otherwise)])
      heap finalEnv finalHeap) :
    BlockContinues module env [.rangeStepLoop name next stop stride body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  refine .next ?_ (rest following anchors stack)
  simp [step, continues, List.append_assoc]

theorem range_done (finished : Calls.rangeContinues next stop stride = false)
    (rest : BlockContinues module env otherwise heap finalEnv finalHeap) :
    BlockContinues module env [.rangeStepLoop name next stop stride body otherwise]
      heap finalEnv finalHeap :=
  fun following anchors stack => .next (by simp [step, finished]) (rest following anchors stack)

theorem loop_resume (rest : BlockContinues module env [next] heap finalEnv finalHeap) :
    BlockContinues module env [.loopResume next] heap finalEnv finalHeap :=
  fun following anchors stack => .next rfl (rest following anchors stack)

theorem returns (first : BlockContinues module env body heap middleEnv middleHeap)
    (rest : BlockReturns module middleEnv following middleHeap answer finalHeap) :
    BlockReturns module env (body ++ following) heap answer finalHeap :=
  fun anchors stack => (first following anchors stack).trans (rest anchors stack)

end BlockContinues

/-- Emission keeps the current comprehension locals and appends the actual value,
including shared references, after evaluating the element's effects. -/
theorem BlockContinues.comprehension_append
    (evaluated : Evaluates module env expression heap value middle)
    (found : middle[address]? = some (.list items)) :
    BlockContinues module env [.comprehensionAppend address expression] heap env
      (middle.set address (.list (items ++ [value]))) := by
  intro following anchors stack
  apply Reaches.next rfl
  apply (Evaluates.arguments_reach (.cons evaluated .nil) (.append address) [] anchors _).trans
  exact .next (following := ⟨.value (.scalar .none), .discard following env :: stack,
    middle.set address (.list (items ++ [value]))⟩)
    (by simp [step, result, run, primitive, Mutable.appendItem, found, Except.map])
    (.next rfl .refl)

/-- Prove a range comprehension by composing ordinary loop proofs. Only its
first range arguments use the enclosing scope. -/
theorem Evaluates.list_comp_range
    (arguments : Arguments module env expressions heap values middle)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (executed : BlockContinues module
      (comprehensionEnv env ((name, .call (.name "range") expressions, filters) :: generators))
      [.rangeStepLoop name start stop stride
        (comprehensionFilters filters (comprehensionBody middle.length element generators)) []]
      (middle ++ [.list []]) finalEnv finalHeap) :
    Evaluates module env
      (.listComp element ((name, .call (.name "range") expressions, filters) :: generators))
      heap (.ref middle.length) finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments _ [] anchors stack).trans
  exact .next (by simp [step, comprehensionStart, bounds])
    ((executed [] anchors (.comprehensionResult middle.length :: stack)).trans
      (.next rfl (.next rfl .refl)))

/-- The first sequence is evaluated and validated outside the comprehension's
local scope; the loop continues to read the same shared object. -/
theorem Evaluates.list_comp_sequence
    (ordinary : ∀ expressions, iterable ≠ .call (.name "range") expressions)
    (evaluated : Evaluates module env iterable heap value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, middle))
    (executed : BlockContinues module
      (comprehensionEnv env ((name, iterable, filters) :: generators))
      [.sequenceStepLoop name (sequenceSource value) 0
        (comprehensionFilters filters (comprehensionBody middle.length element generators)) []]
      (middle ++ [.list []]) finalEnv finalHeap) :
    Evaluates module env (.listComp element ((name, iterable, filters) :: generators))
      heap (.ref middle.length) finalHeap := by
  intro anchors stack
  have first : step module anchors
      ⟨.expr (.listComp element ((name, iterable, filters) :: generators)) env, stack, heap⟩ =
      .next (argumentsState
        (.comprehension element ((name, iterable, filters) :: generators)
          (comprehensionEnv env ((name, iterable, filters) :: generators)))
        env [] [iterable] stack heap) := by
    cases iterable <;> simp_all [step]
  apply Reaches.next first
  apply (arguments_reach (.cons evaluated .nil) _ [] anchors stack).trans
  refine .next ?_
    ((executed [] anchors (.comprehensionResult middle.length :: stack)).trans
      (.next rfl (.next rfl .refl)))
  cases iterable <;> simp_all [step, comprehensionStart, run]
end FormalSW.PyAst.HeapCalls

namespace FormalSW.PyAst.Mutable.Call

/-- Heap execution coverage includes exceptional completion with its final heap. -/
def Supported (call : Call) : Prop := call.execution.Supported

theorem Returns.supported {call : Call} (h : call.Returns) : call.Supported := by
  obtain ⟨value, globals, heap, anchors, run⟩ := h
  exact Execution.supported_of_finishes run

end FormalSW.PyAst.Mutable.Call
