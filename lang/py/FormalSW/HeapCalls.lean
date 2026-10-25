import lang.py.FormalSW.Instances
import lang.py.FormalSW.Linking
import lang.py.FormalSW.ScalarSort
import lang.py.FormalSW.HeapSort
import lang.py.FormalSW.Permutations
import lang.py.FormalSW.StringReplace

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

/-- Each call starts with its own locals. Module bindings share their heap objects;
whole-function locals mask globals even before the first assignment. -/
def functionEnv (args : List Arg) (body : List Stmt) (values : List Value)
    (globals : Mutable.Globals) : Env :=
  match globals with
  | [] => argumentEnv args values
  | _ :: _ => fun name =>
      if name ∈ args.map Arg.name then argumentEnv args values name
      else if name ∈ blockLocals body then none else globals.lookup name

@[simp] theorem functionEnv_empty (args : List Arg) (body : List Stmt) (values : List Value) :
    functionEnv args body values [] = argumentEnv args values := rfl

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

/-- Identity never calls equality methods or coerces Boolean/integer values. -/
def identity : Value → Value → Eval Value
  | .ref left, .ref right => pure (.scalar (.bool (left == right)))
  | .scalar left, .scalar right =>
      scalarResult ((scalarIdentity left right).map (fun value => .ok (.bool value)))
  | _, _ => pure (.scalar (.bool false))

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

/-- Dictionary equality ignores insertion order and compares the stored values. -/
def equalEntries (left right : List (Constant × Value)) : Option Bool :=
  match left with
  | [] => some true
  | (key, value) :: rest => do
      match ScalarDict.lookup right key with
      | none => return false
      | some other =>
          if ← equalElements [value] [other] then equalEntries rest right else return false

def equalDictionaries (left right : List (Constant × Value)) : Option Bool :=
  if left.length = right.length then equalEntries left right else some false

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

/-- Key equality is structural; dictionary values use the existing partial value equality. -/
private def equalKeyEntries : List (HashDict.Entry Value) → List (HashDict.Entry Value) → Option Bool
  | [], _ => some true
  | entry :: rest, right => do
      let some value := HashDict.lookup right entry.1 | some false
      let equal ← equalLists [entry.2.2] [value]
      if equal then equalKeyEntries rest right else some false

private def equalKeyDictionaries (left right : List (HashDict.Entry Value)) : Option Bool :=
  if left.length = right.length then equalKeyEntries left right else some false

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
      | some (.set xs), some (.keySet ys) =>
          return .scalar (.bool (Mutable.compareKeySets op (xs.map fun x => (.scalar x, .scalar x)) ys))
      | some (.keySet xs), some other =>
          match Mutable.keyEntries other with
          | some ys => return .scalar (.bool (Mutable.compareKeySets op xs ys))
          | none => compareDifferent op
      | some (.instance _ _ _), some (.instance _ _ _) =>
          match op with
          | .eq => return .scalar (.bool (a == b))
          | .notEq => return .scalar (.bool (a != b))
          | _ => Mutable.error "TypeError"
      | some (.dataInstance origin name frozen declared fields),
          some (.dataInstance otherOrigin otherName otherFrozen otherDeclared otherFields) =>
          if origin ≠ otherOrigin ∨ name ≠ otherName then compareDifferent op
          else if frozen ≠ otherFrozen ∨ declared ≠ otherDeclared then Mutable.unsupported
          else match op with
          | .eq | .notEq =>
              let left ← declared.mapM fun field => match fields.lookup field with
                | some value => pure value
                | none => Mutable.error "AttributeError"
              let right ← declared.mapM fun field => match otherFields.lookup field with
                | some value => pure value
                | none => Mutable.error "AttributeError"
              let some equal := equalLists left right | Mutable.unsupported
              return .scalar (.bool (if op == .eq then equal else !equal))
          | _ => Mutable.error "TypeError"
      | some (.dict xs), some (.dict ys) =>
          match op with
          | .eq | .notEq =>
              let some equal := if a = b then some true else equalDictionaries xs ys | Mutable.unsupported
              return .scalar (.bool (if op == .eq then equal else !equal))
          | _ => Mutable.error "TypeError"
      | some (.dict xs), some (.keyDict ys) =>
          match op with
          | .eq | .notEq =>
              let some equal := equalKeyDictionaries (Mutable.promoteDictionary xs) ys | Mutable.unsupported
              return .scalar (.bool (if op == .eq then equal else !equal))
          | _ => Mutable.error "TypeError"
      | some (.keyDict xs), some object =>
          match Mutable.dictionaryEntries object with
          | none => compareDifferent op
          | some ys => match op with
              | .eq | .notEq =>
                  let some equal := if a = b then some true else equalKeyDictionaries xs ys | Mutable.unsupported
                  return .scalar (.bool (if op == .eq then equal else !equal))
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

/-- Sequence membership stops at the first identical or equal element. Unsupported
equality is retained rather than silently treated as inequality. -/
def sequenceContains (needle : Value) : List Value → Eval Bool
  | [] => pure false
  | item :: rest => do
      if item = needle then return true
      let equal ← compare .eq item needle
      if ← Mutable.truth equal then return true
      sequenceContains needle rest

/-- Python membership can convert a mutable set needle to a frozenset. That
protocol remains unsupported; ordinary tuple and scalar keys use builtin hashing. -/
def membershipKey (needle : Value) : Eval HashKey := do
  match needle with
  | .ref address => match (← get)[address]? with
      | some (.set _) | some (.keySet _) => Mutable.unsupported
      | _ => Mutable.hashKey needle
  | _ => Mutable.hashKey needle

/-- Membership covers shared sequences, sets and dictionary keys. Other iterable
protocols remain partial; a known non-iterable scalar raises Python's TypeError. -/
def membership (needle container : Value) (negated : Bool) : Eval Value := do
  let found ← match container with
    | .ref address => match (← get)[address]? with
        | some (.list items) | some (.tuple items) => sequenceContains needle items
        | some (.dict entries) =>
            match needle with
            | .scalar key => pure (ScalarDict.lookup entries key).isSome
            | .ref _ => do
                let key ← Mutable.hashKey needle
                pure (HashDict.lookup (Mutable.promoteDictionary entries) key).isSome
        | some (.keyDict entries) => do
            let key ← Mutable.hashKey needle
            pure (HashDict.lookup entries key).isSome
        | some (.set items) => match needle with
            | .scalar value => pure (ScalarSet.contains items value)
            | .ref _ => do
                let key ← membershipKey needle
                pure (Mutable.keyContains (items.map fun x => (.scalar x, .scalar x)) key)
        | some (.keySet items) => do
            let key ← membershipKey needle
            pure (Mutable.keyContains items key)
        | _ => Mutable.unsupported
    | .scalar (.string text) => match needle with
        | .scalar (.string substring) => pure (Strings.contains text substring)
        | _ => Mutable.error "TypeError"
    | .scalar (.int _) | .scalar (.bool _) | .scalar .none => Mutable.error "TypeError"
    | _ => Mutable.unsupported
  return .scalar (.bool (if negated then !found else found))

/-- Substring membership changes no heap objects; operand effects have already run. -/
theorem membership_string (heap : Heap) (text substring : String) (negated : Bool) :
    membership (.scalar (.string substring)) (.scalar (.string text)) negated heap =
      some (.ok (.scalar (.bool (if negated then !Strings.contains text substring
        else Strings.contains text substring))), heap) := by
  simp [membership]

/-- Dictionary membership checks normalized scalar keys without reading their values. -/
theorem membership_dictionary (key : Constant) (negated : Bool)
    (found : heap[address]? = some (.dict entries)) :
    membership (.scalar key) (.ref address) negated heap =
      some (.ok (.scalar (.bool (if negated then !(ScalarDict.lookup entries key).isSome
        else (ScalarDict.lookup entries key).isSome))), heap) := by
  simp [membership, found]

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
      | some (.set _) | some (.keySet _) | some (.dict _) | some (.keyDict _) | some (.tuple _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => Mutable.binary op left right
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
                    | some (.list _) | some (.set _) | some (.keySet _) | some (.dict _) | some (.keyDict _) | some (.tuple _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => Mutable.error "TypeError"
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

/-- Builtins that consume a fresh generator completely before processing its items. -/
inductive GeneratorAction where
  | list
  | sorted
  | join (separator : String)

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
  | pop (address : Nat)
  | sort (address : Nat)
  | replace (text : String)
  | zfill (text : String)
  | join (separator : String)
  | add (address : Nat)
  | dictionaryGet (address : Nat)
  | dictionarySetDefault (address : Nat)
  | builtin (name : Builtin)
  | reversedList
  | sumSequence
  | membership (negated : Bool)
  | sumGenerator (element : Expr) (generators : List (String × Expr × List Expr)) (env : Env) (start : Expr)
  | comprehension (element : Expr) (generators : List (String × Expr × List Expr)) (env : Env)
  | comprehensionTargets (element : Expr) (generators : List (Expr × Expr × List Expr)) (env : Env)
  | setComprehension (element : Expr) (generators : List (Expr × Expr × List Expr)) (env : Env)
  | permutationStart (target : Expr) (body otherwise following : List Stmt) (env : Env)
  | zipStart (target : Expr) (body otherwise following : List Stmt) (env : Env)
  | sumGeneratorTargets (element : Expr) (generators : List (Expr × Expr × List Expr)) (env : Env) (start : Expr)
  | truthGenerator (universal : Bool) (element : Expr) (generators : List (Expr × Expr × List Expr)) (env : Env)
  | generatorCollect (action : GeneratorAction) (element : Expr) (generators : List (Expr × Expr × List Expr)) (env : Env)

/-- The sequence reference and lexical key environment persist across key calls. -/
structure SequenceExtremum where
  maximum : Bool
  source : Value
  parameter : String
  key : Expr
  env : Env

inductive Frame where
  | extremumSource (maximum : Bool) (parameter : String) (key : Expr) (env : Env)
  | extremumKey (cursor : SequenceExtremum) (position : Nat) (candidate : Value) (best : Option (Value × Value))
  | dictionaryKey (value : Expr) (rest : List (Expr × Expr)) (entries : List (Constant × Value)) (env : Env)
  | dictionaryValue (key : Constant) (rest : List (Expr × Expr)) (entries : List (Constant × Value)) (env : Env)
  | sumStart (loop : Stmt) (env : Env)
  /-- Installed after the first iterable and ordinary consumer arguments finish. -/
  | generatorEnd
  | generatorConsumer (action : GeneratorAction)
  | generatorReceiver (element : Expr) (generators : List (Expr × Expr × List Expr)) (env : Env)
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
  | reverseSequence (name : String) (body otherwise following : List Stmt) (env : Env)
  | sequence (name : String) (body otherwise following : List Stmt) (env : Env)
  | unpackSequence (names : List String) (body otherwise following : List Stmt) (env : Env)
  | enumerateSource (index name : String) (start : Expr) (body otherwise following : List Stmt) (env : Env)
  | enumerateStart (index name : String) (source : Value) (body otherwise following : List Stmt) (env : Env)
  | augmentItemReceiver (index : Expr) (op : BinOp) (right : Expr) (rest : List Stmt) (env : Env)
  | augmentItemIndex (receiver : Value) (op : BinOp) (right : Expr) (rest : List Stmt) (env : Env)
  | writeItem (receiver index : Value) (rest : List Stmt) (env : Env)
  | assignItem (base index : Expr) (rest : List Stmt) (env : Env)
  | assignSlice (base lower upper stride : Expr) (rest : List Stmt) (env : Env)
  | rangeArguments (name : String) (done : List Value) (rest : List Expr)
      (body otherwise following : List Stmt) (env : Env)

inductive Work where
  | extremumLoop (cursor : SequenceExtremum) (position : Nat) (best : Option (Value × Value))
  | dictionary (remaining : List (Expr × Expr)) (entries : List (Constant × Value)) (env : Env)
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

def Frame.inGenerator : Frame → Bool
  | .generatorEnd => true
  | _ => false

/-- Preserve the heap and roots when a generator translates StopIteration. -/
def protectGenerator (stack : List Frame) : Step State Completion → Step State Completion
  | .done (.ok completion) => .done (.ok { completion with outcome := match completion.outcome with
      | .error error => .error (Calls.generatorException (stack.any Frame.inGenerator) error)
      | .ok value => .ok value })
  | transition => transition

@[simp] theorem protectGenerator_next (stack : List Frame) (state : State) :
    protectGenerator stack (.next state) = .next state := rfl

@[simp] theorem protectGenerator_unsupported (stack : List Frame) :
    protectGenerator stack .unsupported = .unsupported := rfl

@[simp] theorem protectGenerator_ne_unsupported (stack : List Frame) (transition : Step State Completion) :
    protectGenerator stack transition ≠ .unsupported ↔ transition ≠ .unsupported := by
  cases transition with
  | next => simp
  | unsupported => simp
  | done result => cases result <;> simp [protectGenerator]

def done (anchors : Nat) (heap : Heap) (outcome : Except ExceptionObject Value) (globals : Mutable.Globals := []) : Step State Completion :=
  .done (.ok ⟨outcome, globals, heap, anchors⟩)

def run (anchors : Nat) (heap : Heap) (action : Eval α)
    (next : α → Heap → Step State Completion) (globals : Mutable.Globals := []) : Step State Completion :=
  match action heap with
  | none => .unsupported
  | some (.error error, heap) => done (globals := globals) anchors heap (.error error)
  | some (.ok value, heap) => next value heap

def result (anchors : Nat) (heap : Heap) (action : Eval Value) (stack : List Frame) (globals : Mutable.Globals := []) : Step State Completion :=
  run (globals := globals) anchors heap action fun value heap => .next ⟨.value value, stack, heap⟩

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

/-- Each iterator advance observes the current shared sequence, including key effects. -/
def extremumItem (source : Value) (position : Nat) : Eval (Option Value) := do
  let items ← Mutable.sequence source
  return items[position]?

/-- Keep the original item and first equal key; comparisons may raise on mixed keys. -/
def SequenceExtremum.choose (cursor : SequenceExtremum) (candidate score : Value)
    (best : Option (Value × Value)) : Eval (Value × Value) := do
  match best with
  | none => return (candidate, score)
  | some (winner, previous) =>
      let compared ← compare (if cursor.maximum then .gt else .lt) score previous
      let better ← Mutable.truth compared
      return if better then (candidate, score) else (winner, previous)

/-- Capture positional permutations after all constructor arguments evaluate. -/
def permutationRows : List Value → Eval (List (List SequenceSource))
  | [source, length] => do
      let cursor ← Permutations.acquire source length
      return cursor.remaining.map (List.map sequenceSource)
  | _ => Mutable.error "TypeError"

/-- All argument expressions finish before zip acquires any of its iterators. -/
def zipSources (values : List Value) : Eval (List SequenceSource) :=
  values.mapM fun value => do
    let _ ← Mutable.sequence value
    pure (sequenceSource value)

/-- Fetch fields left to right, stopping at the first exhausted sequence. The
iterators are private; each retained source is read from the current shared heap. -/
def zipFields : List SequenceSource → Nat → Eval (Option (List Value))
  | [], _ => pure (some [])
  | source :: rest, position => do
      let items ← Mutable.sequence (sequenceValue source)
      match items[position]? with
      | none => pure none
      | some value =>
          let more ← zipFields rest position
          pure (more.map (value :: ·))

/-- zip() is empty rather than an infinite sequence of empty tuples. -/
def zipItem (sources : List SequenceSource) (position : Nat) : Eval (Option (List Value)) :=
  match sources with
  | [] => pure none
  | _ :: _ => zipFields sources position

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
    (values : List Value) (stack : List Frame) (heap : Heap) (globals : Mutable.Globals := []) : Step State Completion :=
  match generators with
  | [] => .unsupported
  | (name, iterable, filters) :: rest =>
      let body := comprehensionFilters filters (comprehensionBody heap.length element rest)
      let enter := fun loop => Step.next
        ⟨.block [loop] env, .comprehensionResult heap.length :: stack, heap ++ [.list []]⟩
      match iterable with
      | .call (.name "range") _ => match rangeBounds values with
          | .ok (start, stop, stride) => enter (.rangeStepLoop name start stop stride body [])
          | .error error => done (globals := globals) anchors heap (.error error)
      | _ => match values with
          | [value] => run (globals := globals) anchors heap (Mutable.sequence value) fun _ heap =>
              .next ⟨.block [.sequenceStepLoop name (sequenceSource value) 0 body []] env,
                .comprehensionResult heap.length :: stack, heap ++ [.list []]⟩
          | _ => .unsupported

/-- Enumerate accepts an integer start, including a Boolean, with no size limit. -/
def enumerateStart : Value → Eval Int
  | .scalar (.int value) => pure value
  | .scalar (.bool value) => pure (if value then 1 else 0)
  | _ => Mutable.error "TypeError"

/-- Only immediately unpacked enumerate pairs are admitted by the source checker. -/
def enumerateTarget : Expr → Option (String × String)
  | .tuple [.name index, .name name] | .list [.name index, .name name] => some (index, name)
  | _ => none

/-- Mask every bound name, including unpacked names in later generators. -/
def comprehensionTargetsEnv (env : Env) (generators : List (Expr × Expr × List Expr)) : Env :=
  fun name => if generators.any (fun generator => (targetLocals generator.1).contains name) then none else env name

/-- This internal iterator binding is inaccessible to Python source. -/
def comprehensionTargetName : Expr → String
  | .name name => name
  | _ => "$formalsw.unpack"

/-- Unpacking occurs once per iteration, before any filter or nested loop. -/
def comprehensionTargetBody (target : Expr) (body : List Stmt) : List Stmt :=
  match target with
  | .name _ => body
  | .tuple targets | .list targets =>
      .assign [.tuple targets] (.name "$formalsw.unpack") :: body
  | _ => [.unsupported "unsupported comprehension target"]

/-- Subsequent iterables use the existing for-loop and unpacking semantics. -/
def comprehensionTargetsBody (terminal : List Stmt) : List (Expr × Expr × List Expr) → List Stmt
  | [] => terminal
  | (target, iterable, filters) :: rest =>
      let body := comprehensionTargetBody target
        (comprehensionFilters filters (comprehensionTargetsBody terminal rest))
      match iterable with
      | .zipIterable expressions => [.forZip (.name (comprehensionTargetName target)) expressions body []]
      | .call (.name "enumerate") _ => [.forIn target iterable
          (comprehensionFilters filters (comprehensionTargetsBody terminal rest)) []]
      | _ => [.forIn (.name (comprehensionTargetName target)) iterable body []]

/-- Capture the first iterator in the outer scope, before allocating the result. -/
def comprehensionTargetsStart (anchors : Nat) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) (env : Env)
    (values : List Value) (stack : List Frame) (heap : Heap) (globals : Mutable.Globals := []) (isSet : Bool := false) : Step State Completion :=
  match generators with
  | [] => .unsupported
  | (target, iterable, filters) :: rest =>
      let terminal := if isSet then Stmt.comprehensionAdd heap.length element else .comprehensionAppend heap.length element
      let body := comprehensionTargetBody target
        (comprehensionFilters filters (comprehensionTargetsBody [terminal] rest))
      let name := comprehensionTargetName target
      let enter := fun loop heap => Step.next
        ⟨.block [loop] env, .comprehensionResult heap.length :: stack, heap ++ [if isSet then .set [] else .list []]⟩
      match iterable with
      | .permutationsIterable _ => run (globals := globals) anchors heap (permutationRows values) fun rows heap =>
          enter (.permutationStepLoop name rows body []) heap
      | .zipIterable _ => run (globals := globals) anchors heap (zipSources values) fun sources heap =>
          enter (.zipStepLoop name sources 0 body []) heap
      | .call (.name "enumerate") _ => match enumerateTarget target, values with
          | some (index, name), [source, start] =>
              run (globals := globals) anchors heap (enumerateStart start) fun counter heap =>
                run (globals := globals) anchors heap (Mutable.sequence source) fun _ heap =>
                  enter (.enumerateStepLoop index name (sequenceSource source) 0 counter
                    (comprehensionFilters filters (comprehensionTargetsBody [terminal] rest)) []) heap
          | _, _ => .unsupported
      | .call (.name "range") _ => match rangeBounds values with
          | .ok (first, stop, stride) => enter (.rangeStepLoop name first stop stride body []) heap
          | .error error => done (globals := globals) anchors heap (.error error)
      | _ => match values with
          | [value] => run (globals := globals) anchors heap (Mutable.sequence value) fun _ heap =>
              enter (.sequenceStepLoop name (sequenceSource value) 0 body []) heap
          | _ => .unsupported

/-- A generator's first iterable is evaluated in the enclosing scope. -/
def generatorArguments (action : GeneratorAction) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) (env : Env) (stack : List Frame) (heap : Heap) : State :=
  let expressions := match generators with
    | (_, iterable, _) :: _ => match iterable with
        | .call (.name "range") expressions | .call (.name "enumerate") expressions | .zipIterable expressions | .permutationsIterable expressions => expressions
        | _ => [iterable]
    | [] => []
  argumentsState (.generatorCollect action element generators (comprehensionTargetsEnv env generators))
    env [] expressions stack heap

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
    (stack : List Frame) (heap : Heap) (globals : Mutable.Globals := []) : Step State Completion :=
  run (globals := globals) anchors heap (sumInitial value) fun value heap =>
    .next ⟨.block [loop, .return (.name sumAccumulator)] (setLocal env sumAccumulator value), stack, heap⟩

/-- Ordinary call arguments finish evaluating before the iterable is validated. -/
def sumSequenceStart (anchors : Nat) (values : List Value)
    (stack : List Frame) (heap : Heap) (globals : Mutable.Globals := []) : Step State Completion :=
  match values with
  | [source, start] => run (globals := globals) anchors heap (Mutable.sequence source) fun _ heap =>
      sumEnter (globals := globals) anchors (.sequenceStepLoop sumItem (sequenceSource source) 0 (sumBody (.name sumItem) []) [])
        (fun _ => none) start stack heap
  | _ => .unsupported

/-- Generator creation validates its first iterator before evaluating the starting value.
Subsequent iterables, filters, and elements remain lazy. -/
def sumGeneratorStart (anchors : Nat) (element : Expr)
    (generators : List (String × Expr × List Expr)) (env : Env) (start : Expr)
    (values : List Value) (stack : List Frame) (heap : Heap) (globals : Mutable.Globals := []) : Step State Completion :=
  match generators with
  | [] => .unsupported
  | (name, iterable, filters) :: rest =>
      let body := comprehensionFilters filters (sumBody element rest)
      let enter := fun loop heap => Step.next
        ⟨.expr start env, .sumStart loop (comprehensionEnv env generators) :: stack, heap⟩
      match iterable with
      | .call (.name "range") _ => match rangeBounds values with
          | .ok (first, stop, stride) => enter (.rangeStepLoop name first stop stride body []) heap
          | .error error => done (globals := globals) anchors heap (.error error)
      | _ => match values with
          | [value] => run (globals := globals) anchors heap (Mutable.sequence value) fun _ heap =>
              enter (.sequenceStepLoop name (sequenceSource value) 0 body []) heap
          | _ => .unsupported

/-- Generator sums bind unpacked targets only when iteration begins, after the start argument. -/
def sumGeneratorTargetsStart (anchors : Nat) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) (env : Env) (start : Expr)
    (values : List Value) (stack : List Frame) (heap : Heap) (globals : Mutable.Globals := []) : Step State Completion :=
  match generators with
  | [] => .unsupported
  | (target, iterable, filters) :: rest =>
      let body := comprehensionTargetBody target
        (comprehensionFilters filters (comprehensionTargetsBody (sumBody element []) rest))
      let name := comprehensionTargetName target
      let enter := fun loop heap => Step.next
        ⟨.expr start env, .sumStart loop (comprehensionTargetsEnv env generators) :: stack, heap⟩
      match iterable with
      | .permutationsIterable _ => run (globals := globals) anchors heap (permutationRows values) fun rows heap =>
          enter (.permutationStepLoop name rows body []) heap
      | .zipIterable _ => run (globals := globals) anchors heap (zipSources values) fun sources heap =>
          enter (.zipStepLoop name sources 0 body []) heap
      | .call (.name "enumerate") _ => match enumerateTarget target, values with
          | some (index, name), [source, start] =>
              run (globals := globals) anchors heap (enumerateStart start) fun counter heap =>
                run (globals := globals) anchors heap (Mutable.sequence source) fun _ heap =>
                  enter (.enumerateStepLoop index name (sequenceSource source) 0 counter
                    (comprehensionFilters filters (comprehensionTargetsBody (sumBody element []) rest)) []) heap
          | _, _ => .unsupported
      | .call (.name "range") _ => match rangeBounds values with
          | .ok (first, stop, stride) => enter (.rangeStepLoop name first stop stride body []) heap
          | .error error => done (globals := globals) anchors heap (.error error)
      | _ => match values with
          | [value] => run (globals := globals) anchors heap (Mutable.sequence value) fun _ heap =>
              enter (.sequenceStepLoop name (sequenceSource value) 0 body []) heap
          | _ => .unsupported

/-- Stop on the first decisive truth value; otherwise keep requesting items. -/
def truthBody (universal : Bool) (element : Expr) : List Stmt :=
  [.ifThen element (if universal then [] else [.return (.constant (.bool true))])
    (if universal then [.return (.constant (.bool false))] else [])]

/-- Ordinary all/any arguments are evaluated before their iterator is acquired. -/
def truthSequenceStart (anchors : Nat) (universal : Bool) (values : List Value)
    (stack : List Frame) (heap : Heap) (globals : Mutable.Globals := []) : Step State Completion :=
  match values with
  | [source] => run (globals := globals) anchors heap (Mutable.sequence source) fun _ heap =>
      .next ⟨.block
        [.sequenceStepLoop sumItem (sequenceSource source) 0 (truthBody universal (.name sumItem)) [],
         .return (.constant (.bool universal))] (fun _ => none), stack, heap⟩
  | _ => done (globals := globals) anchors heap (.error { typeName := "TypeError", args := [] })

/-- Evaluate only the first generator iterable in the enclosing lexical scope. -/
def truthGeneratorArguments (universal : Bool) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) (env : Env) (stack : List Frame) (heap : Heap) : State :=
  let expressions := match generators with
    | (_, iterable, _) :: _ => match iterable with
        | .call (.name "range") expressions | .call (.name "enumerate") expressions | .zipIterable expressions | .permutationsIterable expressions => expressions
        | _ => [iterable]
    | [] => []
  argumentsState (.truthGenerator universal element generators (comprehensionTargetsEnv env generators))
    env [] expressions stack heap

/-- Filters, inner iterables, and yielded values stay lazy, including short circuiting.
No collector list is allocated. Exceptions raised by generator code retain its boundary. -/
def truthGeneratorStart (anchors : Nat) (universal : Bool) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) (env : Env)
    (values : List Value) (stack : List Frame) (heap : Heap) (globals : Mutable.Globals := []) : Step State Completion :=
  match generators with
  | [] => .unsupported
  | (target, iterable, filters) :: rest =>
      let terminal := truthBody universal element
      let body := comprehensionTargetBody target
        (comprehensionFilters filters (comprehensionTargetsBody terminal rest))
      let name := comprehensionTargetName target
      let enter := fun loop heap => Step.next
        ⟨.block [loop, .return (.constant (.bool universal))] env, .generatorEnd :: stack, heap⟩
      match iterable with
      | .permutationsIterable _ => run (globals := globals) anchors heap (permutationRows values) fun rows heap =>
          enter (.permutationStepLoop name rows body []) heap
      | .zipIterable _ => run (globals := globals) anchors heap (zipSources values) fun sources heap =>
          enter (.zipStepLoop name sources 0 body []) heap
      | .call (.name "enumerate") _ => match enumerateTarget target, values with
          | some (index, name), [source, start] =>
              run (globals := globals) anchors heap (enumerateStart start) fun counter heap =>
                run (globals := globals) anchors heap (Mutable.sequence source) fun _ heap =>
                  enter (.enumerateStepLoop index name (sequenceSource source) 0 counter
                    (comprehensionFilters filters (comprehensionTargetsBody terminal rest)) []) heap
          | _, _ => .unsupported
      | .call (.name "range") _ => match rangeBounds values with
          | .ok (first, stop, stride) => enter (.rangeStepLoop name first stop stride body []) heap
          | .error error => done (globals := globals) anchors heap (.error error)
      | _ => match values with
          | [value] => run (globals := globals) anchors heap (Mutable.sequence value) fun _ heap =>
              enter (.sequenceStepLoop name (sequenceSource value) 0 body []) heap
          | _ => .unsupported

def primitive : Operation → List Value → Eval Value
  | .membership negated, [needle, container] => membership needle container negated
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
  | .dictionaryGet address, [key] => Mutable.dictionaryGet address key (.scalar .none)
  | .dictionaryGet address, [key, defaultValue] => Mutable.dictionaryGet address key defaultValue
  | .dictionaryGet _, _ => Mutable.error "TypeError"
  | .dictionarySetDefault address, [key] => Mutable.dictionarySetDefault address key (.scalar .none)
  | .dictionarySetDefault address, [key, defaultValue] => Mutable.dictionarySetDefault address key defaultValue
  | .dictionarySetDefault _, _ => Mutable.error "TypeError"
  | .append address, [value] => Mutable.appendItem address value
  | .pop address, [] => Mutable.popItem address (.scalar (.int (-1)))
  | .pop address, [index] => Mutable.popItem address index
  | .pop _, _ => Mutable.error "TypeError"
  | .sort address, [] => do
      let heap ← get
      let some (.list items) := heap[address]? | Mutable.unsupported
      -- Scalar comparisons cannot observe Python's temporary empty sort receiver.
      if !(items.all fun | .scalar _ => true | .ref _ => false) then Mutable.unsupported
      else match HeapSort.sort heap items with
        | some (.ok sorted) =>
            set (heap.set address (.list sorted))
            return .scalar .none
        -- A failed Python sort may partially reorder the list.
        | _ => Mutable.unsupported
  | .sort _, _ => Mutable.error "TypeError"
  | .replace text, [.scalar old, .scalar new] =>
      scalarResult (some (Strings.replaceCall text [old, new]))
  | .replace text, [.scalar old, .scalar new, .scalar count] =>
      scalarResult (some (Strings.replaceCall text [old, new, count]))
  | .replace _, [.scalar (.string _), .scalar (.string _), .ref address] => do
      -- User-defined __index__ protocols are outside the primitive model.
      match (← get)[address]? with
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => Mutable.unsupported
      | _ => Mutable.error "TypeError"
  | .replace _, _ => Mutable.error "TypeError"
  | .zfill text, [.scalar width] => scalarResult (some (Strings.zfillCall text [width]))
  | .zfill _, [.ref address] => do
      match (← get)[address]? with
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) | none => Mutable.unsupported
      | _ => Mutable.error "TypeError"
  | .zfill _, _ => Mutable.error "TypeError"
  | .join separator, [value] => do
      if let .ref address := value then
        match (← get)[address]? with
        | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => Mutable.unsupported
        | _ => pure ()
      let items ← Mutable.sequence value
      let strings ← items.mapM fun item => match item with
        | .scalar (.string text) => pure text
        | _ => Mutable.error "TypeError"
      return .scalar (.string (String.intercalate separator strings))
  | .join _, _ => Mutable.error "TypeError"
  | .add address, [value] => Mutable.addItem address value
  | .append _, _ | .add _, _ => Mutable.error "TypeError"
  | .builtin .identity, [left, right] => identity left right
  | .builtin .len, [value] => Mutable.length value
  | .builtin .pow, [.scalar base, .scalar exponent] => scalarResult (scalarBinary .pow base exponent)
  | .builtin .pow, [base, exponent] => do
      -- Unknown numeric protocols cannot be replaced with a builtin TypeError.
      let heap ← get
      if [base, exponent].any (fun value => match value with
          | .scalar _ => false
          | .ref address => match heap[address]? with
              | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) | none => true
              | _ => false) then Mutable.unsupported
      else Mutable.error "TypeError"
  | .builtin .pow, [.scalar base, .scalar exponent, .scalar modulus] =>
      scalarResult (Calls.modularPower base exponent modulus)
  | .builtin .pow, [base, exponent, modulus] => do
      let heap ← get
      if [base, exponent, modulus].any (fun value => match value with
          | .scalar _ => false
          | .ref address => match heap[address]? with
              | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) | none => true
              | _ => false) then Mutable.unsupported
      else Mutable.error "TypeError"
  | .builtin .pow, _ => Mutable.error "TypeError"
  | .builtin .abs, [.scalar value] => scalarResult (some (Calls.absoluteValue value))
  | .builtin .abs, _ => Mutable.error "TypeError"
  | .builtin .bin, [.scalar value] => scalarResult (some (Strings.bin [value]))
  | .builtin .bin, [.ref address] => do
      match (← get)[address]? with
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => Mutable.unsupported
      | some _ => Mutable.error "TypeError"
      | none => Mutable.unsupported
  | .builtin .bin, _ => Mutable.error "TypeError"
  | .builtin .ord, [.scalar value] => scalarResult (some (Strings.ord value))
  | .builtin .ord, [.ref address] => do
      match (← get)[address]? with
      | some (.bytearray bytes) => scalarResult (some (Strings.ord (.bytes bytes)))
      | some _ => Mutable.error "TypeError"
      | none => Mutable.unsupported
  | .builtin .divmod, values => Mutable.divmod values
  | .builtin .bytearray, values => Mutable.bytearray values
  | .builtin .list, [] => Mutable.allocate []
  | .builtin .list, [value] => do
      -- Custom iteration protocols require their own execution model.
      if let .ref address := value then
        match (← get)[address]? with
        | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => Mutable.unsupported
        | _ => pure ()
      Mutable.allocate (← Mutable.sequence value)
  | .builtin .list, _ => Mutable.error "TypeError"
  | .builtin .set, [] => Mutable.allocateSet []
  | .builtin .setDisplay, values => Mutable.allocateSetValues values
  | .builtin .set, [source] => Mutable.setFrom source
  | .builtin .set, _ => Mutable.error "TypeError"
  | .builtin .sorted, [value] => do
      let items ← match value with
        | .ref address => match (← get)[address]? with
            | some (.set items) => pure (items.map Mutable.Value.scalar)
            | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => Mutable.unsupported
            | _ => Mutable.sequence value
        | _ => Mutable.sequence value
      match HeapSort.sort (← get) items with
      | none => Mutable.unsupported
      | some (.ok values) => Mutable.allocate values
      | some (.error error) => throw error
  | .builtin .intBitLength, [.scalar value] => scalarResult (some (Math.bitLengthCall value))
  | .builtin .intBitLength, [.ref _] => Mutable.error "AttributeError"
  | .builtin .int, [.ref address] => do
      match (← get)[address]? with
      | some (.bytearray bytes) => scalarResult (Calls.integerConversion [.bytes bytes])
      | some (.list _) | some (.set _) | some (.keySet _) | some (.dict _) | some (.keyDict _) | some (.tuple _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => Mutable.error "TypeError"
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
  | .builtin .min, [value] => do
      let items ← match value with
        | .ref address => match (← get)[address]? with
            | some (.set items) => pure (items.map Mutable.Value.scalar)
            | _ => Mutable.sequence value
        | _ => Mutable.sequence value
      let scalars ← items.mapM fun item => match item with
        | .scalar value => pure value
        | .ref _ => Mutable.unsupported
      scalarResult (some (ScalarSet.minimum scalars))
  | .builtin .min, values => do
      let values ← values.mapM fun value => match value with
        | .scalar value => pure value
        | .ref _ => Mutable.unsupported
      scalarResult (Calls.positionalMinimum values)
  | _, _ => Mutable.unsupported

/-- List construction copies the outer list and preserves all element references. -/
theorem primitive_list_list (heap : Heap) (address : Nat) (items : List Value)
    (found : heap[address]? = some (.list items)) :
    primitive (.builtin .list) [.ref address] heap =
      some (.ok (.ref heap.length), heap ++ [.list items]) := by
  simp [primitive, found, Mutable.sequence, Mutable.allocate, Except.map]

/-- Converting a tuple allocates a list without copying the elements. -/
theorem primitive_list_tuple (heap : Heap) (address : Nat) (items : List Value)
    (found : heap[address]? = some (.tuple items)) :
    primitive (.builtin .list) [.ref address] heap =
      some (.ok (.ref heap.length), heap ++ [.list items]) := by
  simp [primitive, found, Mutable.sequence, Mutable.allocate, Except.map]

private theorem mapM_identity (items : List Constant) :
    (items.mapM (fun value => pure value) : Eval (List Constant)) = pure items := by
  simpa using (List.mapM_pure (m := Eval) (l := items) (f := id))

private theorem mapM_strings (items : List String) :
    (items.mapM (fun value => pure value) : Eval (List String)) = pure items := by
  simpa using (List.mapM_pure (m := Eval) (l := items) (f := id))

/-- Joining reads strings in order without modifying the input list. -/
theorem primitive_join_list (heap : Heap) (address : Nat) (separator : String) (items : List String)
    (found : heap[address]? = some (.list (items.map fun text => .scalar (.string text)))) :
    primitive (.join separator) [.ref address] heap =
      some (.ok (.scalar (.string (String.intercalate separator items))), heap) := by
  simp [primitive, found, Mutable.sequence, List.mapM_map, mapM_strings, Function.comp_def, Except.map]

theorem primitive_join_tuple (heap : Heap) (address : Nat) (separator : String) (items : List String)
    (found : heap[address]? = some (.tuple (items.map fun text => .scalar (.string text)))) :
    primitive (.join separator) [.ref address] heap =
      some (.ok (.scalar (.string (String.intercalate separator items))), heap) := by
  simp [primitive, found, Mutable.sequence, List.mapM_map, mapM_strings, Function.comp_def, Except.map]

/-- Sorting reads the list's current contents and returns a fresh list. -/
theorem primitive_sorted_list (heap : Heap) (address : Nat) (items sorted : List Constant)
    (found : heap[address]? = some (.list (items.map Mutable.Value.scalar)))
    (ordered : ScalarSort.sort items = .ok sorted) :
    primitive (.builtin .sorted) [.ref address] heap =
      some (.ok (.ref heap.length), heap ++ [.list (sorted.map Mutable.Value.scalar)]) := by
  simp [primitive, found, Mutable.sequence, HeapSort.sort_scalars,
    ordered, Mutable.allocate, Except.map]

/-- In-place scalar sorting updates the existing cell and returns None. -/
theorem primitive_sort_list (heap : Heap) (address : Nat) (items sorted : List Constant)
    (found : heap[address]? = some (.list (items.map Mutable.Value.scalar)))
    (ordered : ScalarSort.sort items = .ok sorted) :
    primitive (.sort address) [] heap =
      some (.ok (.scalar .none), heap.set address (.list (sorted.map Mutable.Value.scalar))) := by
  simp [primitive, found, HeapSort.sort_scalars, ordered, Except.map]
  have scalarOnly : ¬ ∃ value, value ∈ items.map Mutable.Value.scalar ∧
      (match value with | .scalar _ => true | .ref _ => false)=false := by
    rintro ⟨value, member, impossible⟩
    obtain ⟨item, _, rfl⟩ := List.mem_map.mp member
    cases impossible
  rw [if_neg scalarOnly]
  rfl

theorem primitive_sorted_tuple (heap : Heap) (address : Nat) (items sorted : List Constant)
    (found : heap[address]? = some (.tuple (items.map Mutable.Value.scalar)))
    (ordered : ScalarSort.sort items = .ok sorted) :
    primitive (.builtin .sorted) [.ref address] heap =
      some (.ok (.ref heap.length), heap ++ [.list (sorted.map Mutable.Value.scalar)]) := by
  simp [primitive, found, Mutable.sequence, HeapSort.sort_scalars,
    ordered, Mutable.allocate, Except.map]

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
      | some (.instance origin className fields) | some (.dataInstance origin className _ _ fields) =>
          let body ← instanceClass module origin className
          if name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__" then Mutable.unsupported
          else match fields.lookup name with
          | some _ => pure .notCallable
          | none => match findFunctionIn body name with
              | some (args, body) => pure (.method receiver args body)
              | none => if name.startsWith "__" then Mutable.unsupported else Mutable.error "AttributeError"
      | some (.list _) | some (.bytearray _) =>
          if name = "sort" then match (← get)[address]? with
            | some (.list _) => pure (.sort address)
            | _ => Mutable.error "AttributeError"
          else if name = "append" then pure (.append address)
          else if name = "pop" then pure (.pop address)
          else if name = "get" ∨ name = "setdefault" then Mutable.error "AttributeError"
          else if name = "zfill" then match (← get)[address]? with
            | some (.bytearray _) => Mutable.unsupported
            | _ => Mutable.error "AttributeError"
          else if name = "replace" then match (← get)[address]? with
            | some (.bytearray _) => Mutable.unsupported
            | _ => Mutable.error "AttributeError"
          else Mutable.unsupported
      | some (.set _) | some (.keySet _) =>
          if name = "add" then pure (.add address)
          else if name = "append" ∨ name = "get" ∨ name = "setdefault" ∨ name = "replace" ∨ name = "zfill" ∨ name = "sort" then Mutable.error "AttributeError" else Mutable.unsupported
      | some (.dict _) | some (.keyDict _) =>
          if name = "get" then pure (.dictionaryGet address)
          else if name = "setdefault" then pure (.dictionarySetDefault address)
          else if name = "append" ∨ name = "add" ∨ name = "replace" ∨ name = "zfill" ∨ name = "sort" then Mutable.error "AttributeError" else Mutable.unsupported
      | some (.tuple _) =>
          if name = "append" ∨ name = "add" ∨ name = "get" ∨ name = "setdefault" ∨ name = "pop" ∨ name = "replace" ∨ name = "zfill" ∨ name = "sort" then Mutable.error "AttributeError" else Mutable.unsupported
      | none => Mutable.unsupported
  | .scalar value =>
      if name = "replace" then match value with
        | .string text => pure (.replace text)
        | .bytes _ => Mutable.unsupported
        | _ => Mutable.error "AttributeError"
      else if name = "zfill" then match value with
        | .string text => pure (.zfill text)
        | .bytes _ => Mutable.unsupported
        | _ => Mutable.error "AttributeError"
      else if name = "join" then match value with
        | .string separator => pure (.join separator)
        | .bytes _ => Mutable.unsupported
        | _ => Mutable.error "AttributeError"
      else if name = "append" ∨ name = "add" ∨ name = "get" ∨ name = "setdefault" ∨ name = "pop" ∨ name = "replace" ∨ name = "zfill" ∨ name = "sort" then Mutable.error "AttributeError" else Mutable.unsupported

/-- Stored fields are values; first-class bound methods are outside this model. -/
def getAttribute (module : Module) (receiver : Value) (name : String) : Eval Value := do
  match receiver with
  | .scalar _ => Mutable.unsupported
  | .ref address => match (← get)[address]? with
      | some (.instance origin className fields) | some (.dataInstance origin className _ _ fields) =>
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
    (values : List Value) (stack : List Frame) (heap : Heap) (globals : Mutable.Globals := []) : Step State Completion :=
  match completeArguments args (receiver :: values) with
  | some values => .next ⟨.block (executableBody body) (functionEnv args body values globals), stack, heap⟩
  | none => done (globals := globals) anchors heap (.error { typeName := "TypeError", args := [] })

def dataclassFields : List Stmt → Option (Bool × List Arg)
  | .dataclassFields frozen fields :: _ => some (frozen, fields)
  | _ => none

def construct (module : Module) (anchors : Nat) (name : String) (values : List Value)
    (stack : List Frame) (heap : Heap) (globals : Mutable.Globals := []) : Step State Completion :=
  match module.findClass name with
  | none => .unsupported
  | some (origin, body) =>
      match findFunctionIn body "__init__" with
      | none => match dataclassFields body with
          | some (frozen, fields) => result (globals := globals) anchors heap
              (Mutable.allocateDataclass origin name frozen (fields.map Arg.name) values) stack
          | none => if values.isEmpty then result (globals := globals) anchors heap (Mutable.allocateInstance origin name) stack
              else done (globals := globals) anchors heap (.error { typeName := "TypeError", args := [] })
      | some (args, body) =>
          invokeMethod (globals := globals) anchors (.ref heap.length) args body values (.initialized heap.length :: stack)
            (heap ++ [.instance origin name []])

def step (module : Module) (anchors : Nat) (state : State) (globals : Mutable.Globals := []) : Step State Completion :=
  let ⟨work, stack, heap⟩ := state
  protectGenerator stack <|
  match work with
  | .extremumLoop cursor position best =>
      run (globals := globals) anchors heap (extremumItem cursor.source position) fun item heap =>
        match item with
        | none => match best with
            | none => done (globals := globals) anchors heap (.error { typeName := "ValueError", args := [] })
            | some (winner, _) => .next ⟨.value winner, stack, heap⟩
        | some candidate => .next ⟨.expr cursor.key (setLocal cursor.env cursor.parameter candidate),
            .extremumKey cursor position candidate best :: stack, heap⟩
  | .dictionary [] entries _ => result (globals := globals) anchors heap (Mutable.allocateDict entries) stack
  | .dictionary ((key, value) :: rest) entries env =>
      .next ⟨.expr key env, .dictionaryKey value rest entries env :: stack, heap⟩
  | .startRange name values body otherwise following env =>
      match rangeBounds values with
      | .ok (start, stop, stride) =>
          .next ⟨.block (.rangeStepLoop name start stop stride body otherwise :: following) env, stack, heap⟩
      | .error error => done (globals := globals) anchors heap (.error error)
  | .operation (.call name) values =>
      match findFunctionIn module.body name with
      | some (args, body) =>
          match completeArguments args values with
          | some values => .next ⟨.block (executableBody body) (functionEnv args body values globals), stack, heap⟩
          | none => done (globals := globals) anchors heap (.error { typeName := "TypeError", args := [] })
      | none => match libraryFunction module name with
          | some _ => result (globals := globals) anchors heap (library module name values) stack
          | none => construct (globals := globals) module anchors name values stack heap
  | .operation (.method receiver args body) values =>
      invokeMethod (globals := globals) anchors receiver args body values stack heap
  | .operation (.builtin .all) values => truthSequenceStart (globals := globals) anchors true values stack heap
  | .operation (.builtin .any) values => truthSequenceStart (globals := globals) anchors false values stack heap
  | .operation (.truthGenerator universal element generators env) values =>
      truthGeneratorStart (globals := globals) anchors universal element generators env values stack heap
  | .operation .sumSequence values => sumSequenceStart (globals := globals) anchors values stack heap
  | .operation (.sumGenerator element generators env start) values =>
      sumGeneratorStart (globals := globals) anchors element generators env start values stack heap
  | .operation (.comprehension element generators env) values =>
      comprehensionStart (globals := globals) anchors element generators env values stack heap
  | .operation (.permutationStart target body otherwise following env) values =>
      run (globals := globals) anchors heap (permutationRows values) fun rows heap =>
        .next ⟨.block (.permutationStepLoop (comprehensionTargetName target) rows
          (comprehensionTargetBody target body) otherwise :: following) env, stack, heap⟩
  | .operation (.zipStart target body otherwise following env) values =>
      run (globals := globals) anchors heap (zipSources values) fun sources heap =>
        .next ⟨.block (.zipStepLoop (comprehensionTargetName target) sources 0
          (comprehensionTargetBody target body) otherwise :: following) env, stack, heap⟩
  | .operation (.comprehensionTargets element generators env) values =>
      comprehensionTargetsStart (globals := globals) anchors element generators env values stack heap
  | .operation (.generatorCollect action element generators env) values =>
      comprehensionTargetsStart (globals := globals) anchors element generators env values
        (.generatorEnd :: .generatorConsumer action :: stack) heap
  | .operation (.setComprehension element generators env) values =>
      comprehensionTargetsStart (globals := globals) (isSet := true) anchors element generators env values stack heap
  | .operation (.sumGeneratorTargets element generators env start) values =>
      sumGeneratorTargetsStart (globals := globals) anchors element generators env start values stack heap
  | .operation operation values => result (globals := globals) anchors heap (primitive operation values) stack
  | .expr expression env =>
      match expression with
      | .extremumSequence maximum iterable parameter key =>
          .next ⟨.expr iterable env, .extremumSource maximum parameter key env :: stack, heap⟩
      | .constant value => .next ⟨.value (.scalar value), stack, heap⟩
      | .name name => match env name with
          | some value => .next ⟨.value value, stack, heap⟩
          | none => done (globals := globals) anchors heap (.error { typeName := "UnboundLocalError", args := [] })
      | .attribute base field => .next ⟨.expr base env, .attribute field :: stack, heap⟩
      | .binOp a op b => .next ⟨.expr a env, .binaryLeft op b env false :: stack, heap⟩
      | .unaryOp op expression => .next ⟨.expr expression env, .unary op :: stack, heap⟩
      | .compare a [(op, b)] => .next ⟨.expr a env, .compareLeft op b env :: stack, heap⟩
      | .compare a ((op, b) :: rest) => .next ⟨.expr a env, .chainLeft op b rest env :: stack, heap⟩
      | .boolOp op (first :: rest) => .next ⟨.expr first env, .boolean op rest env :: stack, heap⟩
      | .ifExp test yes no => .next ⟨.expr test env, .conditional yes no env :: stack, heap⟩
      | .dict entries => .next ⟨.dictionary entries [] env, stack, heap⟩
      | .list expressions => .next (argumentsState .list env [] expressions stack heap)
      | .tuple expressions => .next (argumentsState .tuple env [] expressions stack heap)
      | .membership element container negated =>
          .next (argumentsState (.membership negated) env [] [element, container] stack heap)
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
      | .listCompTargets element (generators@((_, iterable, _) :: _)) =>
          let expressions := match iterable with
            | .call (.name "range") expressions | .call (.name "enumerate") expressions | .zipIterable expressions | .permutationsIterable expressions => expressions
            | _ => [iterable]
          .next (argumentsState (.comprehensionTargets element generators (comprehensionTargetsEnv env generators))
            env [] expressions stack heap)
      | .setComp element (generators@((_, iterable, _) :: _)) =>
          let expressions := match iterable with
            | .call (.name "range") expressions | .call (.name "enumerate") expressions | .zipIterable expressions | .permutationsIterable expressions => expressions
            | _ => [iterable]
          .next (argumentsState (.setComprehension element generators (comprehensionTargetsEnv env generators))
            env [] expressions stack heap)
      | .sumGeneratorTargets element (generators@((_, iterable, _) :: _)) start =>
          let expressions := match iterable with
            | .call (.name "range") expressions | .call (.name "enumerate") expressions | .zipIterable expressions | .permutationsIterable expressions => expressions
            | _ => [iterable]
          .next (argumentsState (.sumGeneratorTargets element generators env start) env [] expressions stack heap)
      | .consumeGenerator (.builtinCall .all []) element generators =>
          .next (truthGeneratorArguments true element generators env stack heap)
      | .consumeGenerator (.builtinCall .any []) element generators =>
          .next (truthGeneratorArguments false element generators env stack heap)
      | .consumeGenerator (.builtinCall .list []) element generators =>
          .next (generatorArguments .list element generators env stack heap)
      | .consumeGenerator (.builtinCall .sorted []) element generators =>
          .next (generatorArguments .sorted element generators env stack heap)
      | .consumeGenerator (.attribute receiver "join") element generators =>
          .next ⟨.expr receiver env, .generatorReceiver element generators env :: stack, heap⟩
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
      | .augAssign (.subscript _ (.slice _ _ _)) _ _ :: _ => .unsupported
      | .augAssign (.subscript base index) op expression :: rest =>
          .next ⟨.expr base env, .augmentItemReceiver index op expression rest env :: stack, heap⟩
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
      | .forReversed name iterable body otherwise :: rest =>
          .next ⟨.expr iterable env, .reverseSequence name body otherwise rest env :: stack, heap⟩
      | .reverseSequenceStepLoop name source position body otherwise :: rest =>
          if position < 0 then .next ⟨.block (otherwise ++ rest) env, stack, heap⟩
          else run (globals := globals) anchors heap (Mutable.reversibleSequence (sequenceValue source)) fun items heap =>
            match items[position.toNat]? with
            | none => .next ⟨.block (otherwise ++ rest) env, stack, heap⟩
            | some value => .next ⟨.block (body ++ [Calls.loopContinuation body
                (.reverseSequenceStepLoop name source (position - 1) body otherwise)] ++ rest)
                (setLocal env name value), stack, heap⟩
      | .forIn target (.permutationsIterable expressions) body otherwise :: rest =>
          .next (argumentsState (.permutationStart target body otherwise rest env) env [] expressions stack heap)
      | .permutationStepLoop name rows body otherwise :: rest =>
          match rows with
          | [] => .next ⟨.block (otherwise ++ rest) env, stack, heap⟩
          | row :: remaining =>
              run (globals := globals) anchors heap (Mutable.allocateTuple (row.map sequenceValue)) fun value heap =>
                .next ⟨.block (body ++ [Calls.loopContinuation body
                  (.permutationStepLoop name remaining body otherwise)] ++ rest)
                  (setLocal env name value), stack, heap⟩
      | .forZip target expressions body otherwise :: rest =>
          .next (argumentsState (.zipStart target body otherwise rest env) env [] expressions stack heap)
      | .zipStepLoop name sources position body otherwise :: rest =>
          run (globals := globals) anchors heap (zipItem sources position) fun fields heap =>
            match fields with
            | none => .next ⟨.block (otherwise ++ rest) env, stack, heap⟩
            | some values => run (globals := globals) anchors heap (Mutable.allocateTuple values) fun tuple heap =>
                .next ⟨.block (body ++ [Calls.loopContinuation body
                  (.zipStepLoop name sources (position + 1) body otherwise)] ++ rest)
                  (setLocal env name tuple), stack, heap⟩
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
          run (globals := globals) anchors heap (Mutable.sequence (sequenceValue source)) fun items heap =>
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
          run (globals := globals) anchors heap (Mutable.sequence (sequenceValue source)) fun items heap =>
            match items[position]? with
            | none => .next ⟨.block (otherwise ++ rest) env, stack, heap⟩
            | some value => run (globals := globals) anchors heap (Mutable.sequence value) fun fields heap =>
                if names.length = fields.length then
                  .next ⟨.block (body ++ [Calls.loopContinuation body
                    (.unpackStepLoop names source (position + 1) body otherwise)] ++ rest)
                    (assignNames env names fields), stack, heap⟩
                else done (globals := globals) anchors heap (.error { typeName := "ValueError", args := [] })
      | .sequenceStepLoop name source position body otherwise :: rest =>
          run (globals := globals) anchors heap (Mutable.sequence (sequenceValue source)) fun items heap =>
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
      | .comprehensionAdd address expression :: rest =>
          .next (argumentsState (.add address) env [] [expression] (.discard rest env :: stack) heap)
      | _ => .unsupported
  | .value value =>
      match stack with
      | [] => done (globals := globals) anchors heap (.ok value)
      | frame :: stack => match frame with
          | .dictionaryKey expression rest entries env => match value with
              | .scalar key => .next ⟨.expr expression env, .dictionaryValue key rest entries env :: stack, heap⟩
              -- Hashing can interleave with later expressions differently for
              -- large displays. Stop before these expressions for non-scalar keys.
              | .ref _ => .unsupported
          | .dictionaryValue key rest entries env =>
              .next ⟨.dictionary rest (ScalarDict.insert entries key value) env, stack, heap⟩
          | .sumStart loop env => sumEnter (globals := globals) anchors loop env value (.generatorEnd :: stack) heap
          | .generatorEnd => .next ⟨.value value, stack, heap⟩
          | .generatorConsumer .list => .next ⟨.value value, stack, heap⟩
          | .generatorConsumer .sorted => .next ⟨.operation (.builtin .sorted) [value], stack, heap⟩
          | .generatorConsumer (.join separator) => .next ⟨.operation (.join separator) [value], stack, heap⟩
          | .generatorReceiver element generators env =>
              run (globals := globals) anchors heap (bindMethod module value "join") fun method heap =>
                match method with
                | .join separator => .next (generatorArguments (.join separator) element generators env stack heap)
                | _ => .unsupported
          | .initialized address => match value with
              | .scalar .none => .next ⟨.value (.ref address), stack, heap⟩
              | _ => done (globals := globals) anchors heap (.error { typeName := "TypeError", args := [] })
          | .attribute name => result (globals := globals) anchors heap (getAttribute module value name) stack
          | .methodReceiver name expressions env =>
              run (globals := globals) anchors heap (bindMethod module value name) fun method heap =>
                .next (argumentsState method env [] expressions stack heap)
          | .assignAttribute base name rest env =>
              .next (argumentsState (.setField name value) env [] [base] (.discard rest env :: stack) heap)
          | .augmentAttribute name op right rest env =>
              run (globals := globals) anchors heap (getAttribute module value name) fun previous heap =>
                .next ⟨.expr right env, .binaryRight op previous true ::
                  .writeAttribute value name rest env :: stack, heap⟩
          | .writeAttribute receiver name rest env =>
              result (globals := globals) anchors heap (Mutable.writeField receiver name value) (.discard rest env :: stack)
          | .comprehensionResult address => .next ⟨.value (.ref address), stack, heap⟩
          | .binaryLeft op right env inPlace => .next ⟨.expr right env, .binaryRight op value inPlace :: stack, heap⟩
          | .binaryRight op left inPlace =>
              result (globals := globals) anchors heap (if inPlace then inplace op left value else Mutable.binary op left value) stack
          | .compareLeft op right env => .next ⟨.expr right env, .compareRight op value :: stack, heap⟩
          | .compareRight op left => result (globals := globals) anchors heap (compare op left value) stack
          | .chainLeft op right rest env =>
              .next ⟨.expr right env, .chainRight op value rest env :: stack, heap⟩
          | .chainRight op left rest env =>
              result (globals := globals) anchors heap (compare op left value) (.chainResult value rest env :: stack)
          | .chainResult right rest env => match rest with
              | [] => .next ⟨.value value, stack, heap⟩
              | (op, next) :: rest => run (globals := globals) anchors heap (Mutable.truth value) fun truth heap =>
                  if truth then .next ⟨.expr next env, .chainRight op right rest env :: stack, heap⟩
                  else .next ⟨.value value, stack, heap⟩
          | .unary op => result (globals := globals) anchors heap (unary op value) stack
          | .boolean op rest env => run (globals := globals) anchors heap (Mutable.truth value) fun truth heap =>
              if (match op with | .and => !truth | .or => truth) then .next ⟨.value value, stack, heap⟩
              else match rest with
                | [] => .next ⟨.value value, stack, heap⟩
                | first :: rest => .next ⟨.expr first env, .boolean op rest env :: stack, heap⟩
          | .conditional yes no env => run (globals := globals) anchors heap (Mutable.truth value) fun truth heap =>
              .next ⟨.expr (if truth then yes else no) env, stack, heap⟩
          | .arguments operation done rest env => .next (argumentsState operation env (done ++ [value]) rest stack heap)
          | .addReceiver item env =>
              match value with
              | .ref address => match heap[address]? with
                  | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => run (globals := globals) anchors heap (bindMethod module value "add") fun method heap =>
                      .next (argumentsState method env [] [item] stack heap)
                  | _ => run (globals := globals) anchors heap (Mutable.addReceiver value) fun address heap =>
                      .next (argumentsState (.add address) env [] [item] stack heap)
              | .scalar _ => done (globals := globals) anchors heap (.error { typeName := "AttributeError", args := [] })
          | .appendReceiver item env => match value with
              | .scalar _ => done (globals := globals) anchors heap (.error { typeName := "AttributeError", args := [] })
              | .ref address => match heap[address]? with
                  | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => run (globals := globals) anchors heap (bindMethod module value "append") fun method heap =>
                      .next (argumentsState method env [] [item] stack heap)
                  | _ => run (globals := globals) anchors heap (Mutable.appendReceiver value) fun _ heap =>
                      .next (argumentsState (.append address) env [] [item] stack heap)
          | .augmentItemReceiver index op right rest env =>
              .next ⟨.expr index env, .augmentItemIndex value op right rest env :: stack, heap⟩
          | .augmentItemIndex receiver op right rest env =>
              run (globals := globals) anchors heap (Mutable.getItem receiver value) fun previous heap =>
                .next ⟨.expr right env, .binaryRight op previous true ::
                  .writeItem receiver value rest env :: stack, heap⟩
          | .writeItem receiver index rest env =>
              result (globals := globals) anchors heap (Mutable.setItem receiver index value) (.discard rest env :: stack)
          | .assignItem base index rest env =>
              .next (argumentsState (.setItem value) env [] [base, index] (.discard rest env :: stack) heap)
          | .assignSlice base lower upper stride rest env =>
              .next (argumentsState (.setSlice value) env [] [base, lower, upper, stride]
                (.discard rest env :: stack) heap)
          | .extremumSource maximum parameter key env =>
              run (globals := globals) anchors heap (Mutable.sequence value) fun _ heap =>
                .next ⟨.extremumLoop ⟨maximum, value, parameter, key, env⟩ 0 none, stack, heap⟩
          | .extremumKey cursor position candidate best =>
              run (globals := globals) anchors heap (cursor.choose candidate value best) fun updated heap =>
                .next ⟨.extremumLoop cursor (position + 1) (some updated), stack, heap⟩
          | .assign name rest env => .next ⟨.block rest (setLocal env name value), stack, heap⟩
          | .unpack names rest env =>
              run (globals := globals) anchors heap (Mutable.sequence value) fun items heap =>
                if names.length = items.length then
                  .next ⟨.block rest (assignNames env names items), stack, heap⟩
                else done (globals := globals) anchors heap (.error { typeName := "ValueError", args := [] })
          | .branch yes no rest env => run (globals := globals) anchors heap (Mutable.truth value) fun truth heap =>
              .next ⟨.block ((if truth then yes else no) ++ rest) env, stack, heap⟩
          | .assertion message rest env => run (globals := globals) anchors heap (Mutable.truth value) fun truth heap =>
              if truth then .next ⟨.block rest env, stack, heap⟩
              else match message with
                | none => done (globals := globals) anchors heap (.error { typeName := "AssertionError", args := [] })
                | some expression => .next ⟨.expr expression env, .assertionMessage :: stack, heap⟩
          | .reverseSequence name body otherwise following env =>
              run (globals := globals) anchors heap (Mutable.reversibleSequence value) fun items heap =>
                .next ⟨.block (.reverseSequenceStepLoop name (sequenceSource value)
                  ((items.length : Int) - 1) body otherwise :: following) env, stack, heap⟩
          | .sequence name body otherwise following env =>
              run (globals := globals) anchors heap (Mutable.sequence value) fun _ heap =>
                .next ⟨.block (.sequenceStepLoop name (sequenceSource value) 0 body otherwise :: following) env,
                  stack, heap⟩
          | .unpackSequence names body otherwise following env =>
              run (globals := globals) anchors heap (Mutable.sequence value) fun _ heap =>
                .next ⟨.block (.unpackStepLoop names (sequenceSource value) 0 body otherwise :: following) env,
                  stack, heap⟩
          | .enumerateSource index name start body otherwise following env =>
              .next ⟨.expr start env, .enumerateStart index name value body otherwise following env :: stack, heap⟩
          | .enumerateStart index name source body otherwise following env =>
              run (globals := globals) anchors heap (enumerateStart value) fun counter heap =>
                run (globals := globals) anchors heap (Mutable.sequence source) fun _ heap =>
                  .next ⟨.block (.enumerateStepLoop index name (sequenceSource source) 0 counter body otherwise :: following) env,
                    stack, heap⟩
          | .assertionMessage => match value with
              | .scalar value => done (globals := globals) anchors heap (.error { typeName := "AssertionError", args := [value] })
              -- Exception arguments currently have a scalar observation boundary.
              | .ref _ => .unsupported
          | .discard rest env => .next ⟨.block rest env, stack, heap⟩
          | .rangeArguments name done rest body otherwise following env =>
              .next (rangeState name env (done ++ [value]) rest body otherwise following stack heap)

/-- Entry references stay observable; freshly allocated unreachable lists do not
become roots in the completion's alias-preserving graph. -/
def call (module : Module) (name : String) (values : List Value) (heap : Heap) (globals : Mutable.Globals := []) : Mutable.Call :=
  ⟨⟨State, ⟨.operation (.call name) values, [], heap⟩, step (globals := globals) module heap.length⟩⟩

/-- Preconditions run from the same initial heap as the specified call. Their
private evaluation may allocate or mutate without changing the call's inputs. -/
def evaluate (module : Module) (env : Env) (expression : Expr) (heap : Heap) (globals : Mutable.Globals := []) : Mutable.Call :=
  ⟨⟨State, ⟨.expr expression env, [], heap⟩, step (globals := globals) module heap.length⟩⟩

/-- Only Boolean True satisfies a precondition; other truthy values do not. -/
def Condition (module : Module) (env : Env) (expression : Expr) (heap : Heap) (globals : Mutable.Globals := []) : Prop :=
  ∃ finalHeap, (evaluate (globals := globals) module env expression heap).Finishes
    ⟨.ok (.scalar (.bool true)), globals, finalHeap, heap.length⟩

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

variable {globals : Mutable.Globals}

inductive Reaches (module : Module) (anchors : Nat) : (initial final : State) → (globals : Mutable.Globals := []) → Prop where
  | refl {globals : Mutable.Globals} : Reaches (globals := globals) module anchors state state
  | next {globals : Mutable.Globals} : step (globals := globals) module anchors state = .next following →
      Reaches (globals := globals) module anchors following final → Reaches (globals := globals) module anchors state final

theorem Reaches.trans (h : Reaches (globals := globals) module anchors a b) (rest : Reaches (globals := globals) module anchors b c) :
    Reaches (globals := globals) module anchors a c := by
  induction h with
  | refl => exact rest
  | next h _ ih => exact .next h (ih rest)

theorem Reaches.finishes (h : Reaches (globals := globals) module anchors a b)
    (rest : Finishes (step (globals := globals) module anchors) b outcome) : Finishes (step (globals := globals) module anchors) a outcome := by
  induction h with
  | refl => exact rest
  | next h _ ih => exact .next h (ih rest)

def Evaluates (module : Module) (env : Env) (expression : Expr)
    (heap : Heap) (value : Value) (finalHeap : Heap) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, Reaches (globals := globals) module anchors ⟨.expr expression env, stack, heap⟩ ⟨.value value, stack, finalHeap⟩

/-- Private iterators are consumed by loops, never evaluated as Python values. -/
theorem Evaluates.not_permutations
    (evaluated : Evaluates (globals := globals) module env iterable heap value finalHeap)
    (expressions : List Expr) : iterable ≠ .permutationsIterable expressions := by
  intro equal
  subst iterable
  have reached := evaluated 0 []
  cases reached with
  | next transition _ => simp [step] at transition

theorem Evaluates.finishes (h : Evaluates (globals := globals) module env expression heap value finalHeap) :
    (evaluate (globals := globals) module env expression heap).Finishes ⟨.ok value, globals, finalHeap, heap.length⟩ :=
  (h heap.length []).finishes (.done rfl)

theorem Evaluates.condition_iff (h : Evaluates (globals := globals) module env expression heap value finalHeap) :
    Condition (globals := globals) module env expression heap ↔ value = .scalar (.bool true) := by
  constructor
  · rintro ⟨otherHeap, finished⟩
    have same := h.finishes.unique finished
    cases same
    rfl
  · intro same
    subst value
    exact ⟨finalHeap, h.finishes⟩

def ReturnsValue (module : Module) (name : String) (values : List Value)
    (heap : Heap) (value : Value) (finalHeap : Heap) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, Reaches (globals := globals) module anchors ⟨.operation (.call name) values, stack, heap⟩ ⟨.value value, stack, finalHeap⟩

/-- Reuse a helper result when omitted arguments expand to the already proved
argument vector. Both entry steps bind exactly the same local environment. -/
theorem ReturnsValue.with_defaults
    (found : findFunctionIn module.body name = some (args, body))
    (filled : completeArguments args supplied = some values)
    (complete : completeArguments args values = some values)
    (h : ReturnsValue (globals := globals) module name values heap value finalHeap) :
    ReturnsValue (globals := globals) module name supplied heap value finalHeap := by
  intro anchors stack
  cases h anchors stack with
  | next transition rest =>
      simp only [step, found, complete, protectGenerator_next, Step.next.injEq] at transition
      subst transition
      exact .next (by simp [step, found, filled]) rest

theorem ReturnsValue.finishes (h : ReturnsValue (globals := globals) module name values heap value finalHeap) :
    (call (globals := globals) module name values heap).Finishes ⟨.ok value, globals, finalHeap, heap.length⟩ :=
  (h heap.length []).finishes (.done rfl)

theorem ReturnsValue.returns (h : ReturnsValue (globals := globals) module name values heap value finalHeap) :
    (call (globals := globals) module name values heap).Returns := ⟨value, globals, finalHeap, heap.length, h.finishes⟩

theorem Reaches.scalar_finishes (h : Reaches module 0 a b)
    (rest : Finishes (scalarStep module) b outcome) : Finishes (scalarStep module) a outcome := by
  generalize empty : ([] : Mutable.Globals) = context at h
  induction h with
  | refl => exact rest
  | next transition _ ih =>
      cases empty
      exact .next (by simp [scalarStep, transition]) (ih rest rfl)

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
          | list items | tuple items | bytearray items | set items | keySet items | dict items | keyDict items => simp [bindMethod, found]
          | «instance» origin className fields | dataInstance origin className frozen declared fields =>
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
          | list items | tuple items | bytearray items | set items | keySet items | dict items | keyDict items =>
              simp [getAttribute, found]
          | «instance» origin className fields | dataInstance origin className frozen declared fields =>
              cases defined : source.findClass className with
              | none => simp [getAttribute, found, instanceClass, defined, Mutable.unsupported] at supported
              | some definition =>
                  rcases definition with ⟨identity, body⟩
                  have preserved := (extension.classes className identity body defined).1
                  simp [getAttribute, found, instanceClass, defined, preserved]

private theorem run_extend (left right : Eval α)
    (same : left heap ≠ none → right heap = left heap)
    (supported : run (globals := globals) anchors heap left next ≠ .unsupported) :
    run (globals := globals) anchors heap right next = run (globals := globals) anchors heap left next := by
  have defined : left heap ≠ none := by
    intro missing
    simp [run, missing] at supported
  simp only [run, same defined]

private theorem protected_run_extend (left right : Eval α)
    (same : left heap ≠ none → right heap = left heap)
    (supported : protectGenerator frames (run (globals := globals) anchors heap left next) ≠ .unsupported) :
    protectGenerator frames (run (globals := globals) anchors heap right next) =
      protectGenerator frames (run (globals := globals) anchors heap left next) :=
  congrArg (protectGenerator frames) (run_extend left right same
    ((protectGenerator_ne_unsupported frames _).mp supported))

/-- Imported helpers retain their checked bodies and share the caller's heap. -/
theorem step_extend (extension : Extends target source) (state : State)
    (supported : step (globals := globals) source anchors state ≠ .unsupported) :
    step (globals := globals) target anchors state = step (globals := globals) source anchors state := by
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
      | builtin name => cases name <;> rfl
      | list | tuple | subscript | slice | setItem _ | setSlice _ | append _ | pop _ | sort _ | replace _ | zfill _ | join _ | add _ | dictionaryGet _ | dictionarySetDefault _ | reversedList | sumSequence | membership _ | sumGenerator _ _ _ _ | raiseException _ | comprehension _ _ _ | comprehensionTargets _ _ _ | setComprehension _ _ _ | sumGeneratorTargets _ _ _ _ | generatorCollect _ _ _ _ | truthGenerator _ _ _ _ | permutationStart _ _ _ _ _ | zipStart _ _ _ _ _ | method _ _ _ | notCallable | setField _ _ => rfl
  | dictionary remaining entries env => cases remaining <;> rfl
  | expr _ _ | block _ _ | startRange _ _ _ _ _ _ | extremumLoop _ _ _ => rfl
  | value value =>
      cases stack with
      | nil => rfl
      | cons frame stack =>
          cases frame with
          | «attribute» name =>
              exact protected_run_extend _ _ (attribute_extend extension) supported
          | methodReceiver name arguments env =>
              exact protected_run_extend _ _ (bindMethod_extend extension) supported
          | generatorReceiver element generators env =>
              exact protected_run_extend _ _ (bindMethod_extend extension) supported
          | generatorConsumer action => cases action <;> rfl
          | augmentAttribute name op right rest env =>
              exact protected_run_extend _ _ (attribute_extend extension) supported
          | addReceiver item env | appendReceiver item env =>
              cases value with
              | scalar _ => rfl
              | ref address =>
                  cases found : heap[address]? with
                  | none => simp [step, found]
                  | some object =>
                      cases object with
                      | list items | tuple items | bytearray items | set items | keySet items | dict items | keyDict items => simp [step, found]
                      | «instance» origin className fields | dataInstance origin className frozen declared fields =>
                          simp only [step, found] at supported ⊢
                          exact protected_run_extend _ _ (bindMethod_extend extension) supported
          | _ => rfl

theorem Reaches.extend (h : Reaches (globals := globals) source anchors initial final) (extension : Extends target source) :
    Reaches (globals := globals) target anchors initial final := by
  induction h with
  | refl => exact .refl
  | next transition _ ih =>
      apply Reaches.next _ ih
      rw [step_extend extension _ (by simp [transition])]
      exact transition

theorem ReturnsValue.extend (h : ReturnsValue (globals := globals) source name values heap value finalHeap)
    (extension : Extends target source) : ReturnsValue (globals := globals) target name values heap value finalHeap :=
  fun anchors stack => (h anchors stack).extend extension


namespace Evaluates

theorem constant : Evaluates (globals := globals) module env (.constant value) heap (.scalar value) heap :=
  fun _ _ => .next rfl .refl

theorem lookup (h : env name = some value) : Evaluates (globals := globals) module env (.name name) heap value heap :=
  fun _ _ => .next (by simp [step, h]) .refl

theorem binary (left : Evaluates (globals := globals) module env a heap av middle)
    (right : Evaluates (globals := globals) module env b middle bv afterRight)
    (operation : Mutable.binary op av bv afterRight = some (.ok value, finalHeap)) :
    Evaluates (globals := globals) module env (.binOp a op b) heap value finalHeap := by
  intro anchors stack
  exact .next rfl ((left _ _).trans (.next rfl ((right _ _).trans
    (.next (by simp [step, result, run, operation]) .refl))))

theorem unary (evaluated : Evaluates (globals := globals) module env expression heap value middle)
    (operation : HeapCalls.unary op value middle = some (.ok resultValue, finalHeap)) :
    Evaluates (globals := globals) module env (.unaryOp op expression) heap resultValue finalHeap := by
  intro anchors stack
  exact .next rfl ((evaluated anchors _).trans
    (.next (by simp [step, result, run, operation]) .refl))

theorem compare (left : Evaluates (globals := globals) module env a heap av middle)
    (right : Evaluates (globals := globals) module env b middle bv afterRight)
    (operation : HeapCalls.compare op av bv afterRight = some (.ok value, finalHeap)) :
    Evaluates (globals := globals) module env (.compare a [(op, b)]) heap value finalHeap := by
  intro anchors stack
  exact .next rfl ((left _ _).trans (.next rfl ((right _ _).trans
    (.next (by simp [step, result, run, operation]) .refl))))

/-- Continue a comparison chain with the middle operand's value already evaluated. -/
def Compares (module : Module) (env : Env) (left : Value) (op : CmpOp) (right : Expr)
    (rest : List (CmpOp × Expr)) (heap : Heap) (answer : Value) (finalHeap : Heap) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack,
    Reaches (globals := globals) module anchors ⟨.expr right env, .chainRight op left rest env :: stack, heap⟩
      ⟨.value answer, stack, finalHeap⟩

namespace Compares

theorem last (evaluated : Evaluates (globals := globals) module env right heap value middle)
    (operation : HeapCalls.compare op left value middle = some (.ok answer, finalHeap)) :
    Compares (globals := globals) module env left op right [] heap answer finalHeap := by
  intro anchors stack
  apply (evaluated anchors _).trans
  apply Reaches.next (following :=
    ⟨.value answer, .chainResult value [] env :: stack, finalHeap⟩)
    (by simp [step, result, run, operation])
  exact .next rfl .refl

theorem stop (evaluated : Evaluates (globals := globals) module env right heap value middle)
    (operation : HeapCalls.compare op left value middle = some (.ok answer, finalHeap))
    (truth : Mutable.truth answer finalHeap = some (.ok false, finalHeap)) :
    Compares (globals := globals) module env left op right (next :: rest) heap answer finalHeap := by
  intro anchors stack
  apply (evaluated anchors _).trans
  apply Reaches.next (following :=
    ⟨.value answer, .chainResult value (next :: rest) env :: stack, finalHeap⟩)
    (by simp [step, result, run, operation])
  cases next
  exact .next (by simp [step, run, truth]) .refl

theorem next (evaluated : Evaluates (globals := globals) module env right heap value middle)
    (operation : HeapCalls.compare op left value middle = some (.ok compared, afterComparison))
    (truth : Mutable.truth compared afterComparison = some (.ok true, afterComparison))
    (following : Compares (globals := globals) module env value nextOp nextRight rest afterComparison answer finalHeap) :
    Compares (globals := globals) module env left op right ((nextOp, nextRight) :: rest) heap answer finalHeap := by
  intro anchors stack
  apply (evaluated anchors _).trans
  apply Reaches.next (following :=
    ⟨.value compared, .chainResult value ((nextOp, nextRight) :: rest) env :: stack,
      afterComparison⟩) (by simp [step, result, run, operation])
  exact .next (by simp [step, run, truth]) (following anchors stack)

end Compares

theorem chain (left : Evaluates (globals := globals) module env expression heap value middle)
    (following : Compares (globals := globals) module env value op right (next :: rest) middle answer finalHeap) :
    Evaluates (globals := globals) module env (.compare expression ((op, right) :: next :: rest)) heap answer finalHeap := by
  intro anchors stack
  exact .next rfl ((left anchors _).trans (.next rfl (following anchors stack)))

/-- Short-circuiting returns the first operand without evaluating later expressions. -/
theorem boolean_stop (evaluated : Evaluates (globals := globals) module env first heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (stop : (match op with | .and => !flag | .or => flag) = true) :
    Evaluates (globals := globals) module env (.boolOp op (first :: rest)) heap value middle := by
  intro anchors stack
  exact .next rfl ((evaluated anchors _).trans
    (.next (by simp [step, run, truth, stop]) .refl))

/-- The last operand supplies the result, preserving its value and heap effects. -/
theorem boolean_last (evaluated : Evaluates (globals := globals) module env expression heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle)) :
    Evaluates (globals := globals) module env (.boolOp op [expression]) heap value middle := by
  intro anchors stack
  apply Reaches.next rfl
  apply (evaluated anchors _).trans
  apply Reaches.next _ .refl
  cases op <;> cases flag <;> simp [step, run, truth]

/-- A non-short-circuiting operand continues in the heap it produced. -/
theorem boolean_next (evaluated : Evaluates (globals := globals) module env first heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (continues : (match op with | .and => !flag | .or => flag) = false)
    (rest : Evaluates (globals := globals) module env (.boolOp op (next :: tail)) middle answer finalHeap) :
    Evaluates (globals := globals) module env (.boolOp op (first :: next :: tail)) heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (evaluated anchors _).trans
  cases rest anchors stack with
  | next transition following =>
      simp only [step, protectGenerator_next, Step.next.injEq] at transition
      subst transition
      exact .next (by simp [step, run, truth, continues]) following

theorem conditional (condition : Evaluates (globals := globals) module env test heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (branch : Evaluates (globals := globals) module env (if flag then yes else no) middle answer finalHeap) :
    Evaluates (globals := globals) module env (.ifExp test yes no) heap answer finalHeap := by
  intro anchors stack
  exact .next rfl ((condition anchors _).trans
    (.next (by simp [step, run, truth]) (branch anchors stack)))

inductive Arguments (module : Module) (env : Env) : List Expr → Heap → List Value → Heap → (globals : Mutable.Globals := []) → Prop where
  | nil {globals : Mutable.Globals} : Arguments (globals := globals) module env [] heap [] heap
  | cons {globals : Mutable.Globals} : Evaluates (globals := globals) module env expression heap value middle →
      Arguments (globals := globals) module env expressions middle values finalHeap →
      Arguments (globals := globals) module env (expression :: expressions) heap (value :: values) finalHeap

/-- Argument expressions retain left-to-right effects for every call operation. -/
theorem arguments_reach (h : Arguments (globals := globals) module env expressions heap values finalHeap)
    (operation : Operation) (done : List Value) (anchors : Nat) (stack : List Frame) :
    Reaches (globals := globals) module anchors (argumentsState operation env done expressions stack heap)
      ⟨.operation operation (done ++ values), stack, finalHeap⟩ := by
  induction h generalizing done with
  | nil => simp [argumentsState]; exact .refl
  | @cons expression heap value middle expressions values finalHeap globals head tail ih =>
      apply (head _ _).trans
      refine .next rfl ?_
      simpa [List.append_assoc] using ih (done ++ [value])

theorem call (arguments : Arguments (globals := globals) module env expressions heap values middle)
    (callee : ReturnsValue (globals := globals) module name values middle value finalHeap) :
    Evaluates (globals := globals) module env (.call (.name name) expressions) heap value finalHeap := by
  intro anchors stack
  exact .next rfl ((arguments_reach arguments (.call name) [] anchors stack).trans (callee anchors stack))

theorem library_call (arguments : Arguments (globals := globals) module env expressions heap values middle)
    (absent : findFunctionIn module.body name = none)
    (operation : library module name values middle = some (.ok value, finalHeap)) :
    Evaluates (globals := globals) module env (.call (.name name) expressions) heap value finalHeap := by
  cases imported : libraryFunction module name with
  | none => simp [library, imported, Mutable.unsupported] at operation
  | some implementation =>
      apply call arguments
      intro anchors stack
      exact .next (by simp [step, absent, imported, result, run, operation]) .refl

theorem qualified_call (notAppend : field ≠ "append")
    (arguments : Arguments (globals := globals) module env expressions heap values middle)
    (callee : ReturnsValue (globals := globals) module (alias ++ "." ++ field) values middle value finalHeap)
    (notAdd : field ≠ "add" := by decide)
    (unbound : env alias = none := by rfl) :
    Evaluates (globals := globals) module env (.call (.attribute (.name alias) field) expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := argumentsState (.call (alias ++ "." ++ field)) env [] expressions stack heap)
    (by simp [step, notAppend, notAdd, unbound])
  exact (arguments_reach arguments (.call (alias ++ "." ++ field)) [] anchors stack).trans (callee anchors stack)

theorem list (arguments : Arguments (globals := globals) module env expressions heap values finalHeap) :
    Evaluates (globals := globals) module env (.list expressions) heap (.ref finalHeap.length) (finalHeap ++ [.list values]) := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments .list [] anchors stack).trans
  exact .next (by simp [step, result, run, primitive, Mutable.allocate, Except.map]) .refl

theorem membership
    (arguments : Arguments (globals := globals) module env [element, container] heap [needle, source] middle)
    (tested : HeapCalls.membership needle source negated middle = some (.ok value, finalHeap)) :
    Evaluates (globals := globals) module env (.membership element container negated) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments (.membership negated) [] anchors stack).trans
  exact .next (by simp [step, result, run, primitive, tested]) .refl

/-- Nonempty runtime tuple displays allocate after all their elements evaluate. -/
theorem tuple (arguments : Arguments (globals := globals) module env expressions heap values finalHeap)
    (nonempty : values ≠ []) :
    Evaluates (globals := globals) module env (.tuple expressions) heap (.ref finalHeap.length)
      (finalHeap ++ [.tuple values]) := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments .tuple [] anchors stack).trans
  exact .next (by simp [step, result, run, primitive, Mutable.allocateTuple, nonempty, Except.map]) .refl

/-- Subscription evaluates its receiver and index before reading the shared heap. -/
theorem subscript
    (ordinary : ∀ a b c, index ≠ .slice a b c)
    (receiver : Evaluates (globals := globals) module env base heap value middle)
    (subscript : Evaluates (globals := globals) module env index middle position afterIndex)
    (operation : Mutable.getItem value position afterIndex = some (.ok answer, finalHeap)) :
    Evaluates (globals := globals) module env (.subscript base index) heap answer finalHeap := by
  intro anchors stack
  have start : step (globals := globals) module anchors ⟨.expr (.subscript base index) env, stack, heap⟩ =
      .next ⟨.expr base env, .arguments .subscript [] [index] env :: stack, heap⟩ := by
    cases index <;> simp_all [step, argumentsState]
  apply Reaches.next start
  apply (receiver anchors _).trans
  apply Reaches.next rfl
  apply (subscript anchors _).trans
  apply Reaches.next rfl
  exact .next (by simp [argumentsState, step, primitive, result, run, operation]) .refl

/-- Slice arguments evaluate left to right, retaining effects before allocation. -/
theorem slice (arguments : Arguments (globals := globals) module env
    [base, lower.getD (.constant .none), upper.getD (.constant .none), stride.getD (.constant .none)]
    heap [receiver, first, last, stepValue] middle)
    (operation : Mutable.getSlice receiver first last stepValue middle = some (.ok value, finalHeap)) :
    Evaluates (globals := globals) module env (.subscript base (.slice lower upper stride)) heap value finalHeap := by
  intro anchors stack
  exact .next rfl ((arguments_reach arguments .slice [] anchors stack).trans
    (.next (by simp [step, primitive, result, run, operation]) .refl))

theorem reversed_list (evaluated : Evaluates (globals := globals) module env expression heap (.ref address) middle)
    (found : middle[address]? = some (.list items)) :
    Evaluates (globals := globals) module env (.reversedList expression) heap (.ref middle.length)
      (middle ++ [.list items.reverse]) := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach (.cons evaluated .nil) .reversedList [] anchors stack).trans
  exact .next (by simp [step, result, run, primitive, Mutable.sequence, found,
    Mutable.allocate, Except.map]) .refl

theorem builtin (arguments : Arguments (globals := globals) module env expressions heap values middle)
    (operation : primitive (.builtin name) values middle = some (.ok value, finalHeap)) :
    Evaluates (globals := globals) module env (.builtinCall name expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments (.builtin name) [] anchors stack).trans
  cases name with
  | all | any => simp [primitive, Mutable.unsupported] at operation
  | _ => exact .next (by simp [step, result, run, operation]) .refl

/-- Joining captures the separator before evaluating the iterable argument. -/
theorem join (receiver : Evaluates (globals := globals) module env base heap (.scalar (.string separator)) middle)
    (arguments : Arguments (globals := globals) module env expressions middle values afterArguments)
    (operation : primitive (.join separator) values afterArguments = some (.ok value, finalHeap))
    (localName : ∀ name, base = .name name → (env name).isSome = true) :
    Evaluates (globals := globals) module env (.call (.attribute base "join") expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr base env, .methodReceiver "join" expressions env :: stack, heap⟩)
    (by cases base <;> simp_all [step])
  apply (receiver anchors _).trans
  apply Reaches.next (following := argumentsState (.join separator) env [] expressions stack middle)
    (by simp [step, run, bindMethod])
  apply (arguments_reach arguments (.join separator) [] anchors stack).trans
  exact .next (by simp [step, result, run, operation]) .refl

/-- Replacement captures the string before evaluating arguments left to right.
Argument effects and exceptions use the ordinary call rules. -/
theorem replace (receiver : Evaluates (globals := globals) module env base heap (.scalar (.string text)) middle)
    (arguments : Arguments (globals := globals) module env expressions middle values afterArguments)
    (operation : primitive (.replace text) values afterArguments = some (.ok value, finalHeap))
    (localName : ∀ name, base = .name name → (env name).isSome = true) :
    Evaluates (globals := globals) module env (.call (.attribute base "replace") expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr base env, .methodReceiver "replace" expressions env :: stack, heap⟩)
    (by cases base <;> simp_all [step])
  apply (receiver anchors _).trans
  apply Reaches.next (following := argumentsState (.replace text) env [] expressions stack middle)
    (by simp [step, run, bindMethod])
  apply (arguments_reach arguments (.replace text) [] anchors stack).trans
  exact .next (by simp [step, result, run, operation]) .refl

/-- Zero filling captures its string before the width argument and preserves argument effects. -/
theorem zfill (receiver : Evaluates (globals := globals) module env base heap (.scalar (.string text)) middle)
    (arguments : Arguments (globals := globals) module env expressions middle values afterArguments)
    (operation : primitive (.zfill text) values afterArguments = some (.ok value, finalHeap))
    (localName : ∀ name, base = .name name → (env name).isSome = true) :
    Evaluates (globals := globals) module env (.call (.attribute base "zfill") expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr base env, .methodReceiver "zfill" expressions env :: stack, heap⟩)
    (by cases base <;> simp_all [step])
  apply (receiver anchors _).trans
  apply Reaches.next (following := argumentsState (.zfill text) env [] expressions stack middle)
    (by simp [step, run, bindMethod])
  apply (arguments_reach arguments (.zfill text) [] anchors stack).trans
  exact .next (by simp [step, result, run, operation]) .refl

/-- Successful scalar sorting mutates the captured receiver and returns None. -/
theorem sort (receiver : Evaluates (globals := globals) module env base heap (.ref address) middle)
    (found : middle[address]? = some (.list items))
    (operation : primitive (.sort address) [] middle = some (.ok (.scalar .none), finalHeap))
    (localName : ∀ name, base = .name name → (env name).isSome = true) :
    Evaluates (globals := globals) module env (.call (.attribute base "sort") []) heap (.scalar .none) finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr base env, .methodReceiver "sort" [] env :: stack, heap⟩)
    (by cases base <;> simp_all [step])
  apply (receiver anchors _).trans
  apply Reaches.next (following := argumentsState (.sort address) env [] [] stack middle)
    (by simp [step, run, bindMethod, found])
  exact .next (by simp [argumentsState, step, result, run, operation]) .refl

/-- The receiver is bound before arguments run; removal reads the resulting live heap. -/
theorem pop (lookup : env name = some (.ref address))
    (bound : bindMethod module (.ref address) "pop" heap = some (.ok (.pop address), heap))
    (arguments : Arguments (globals := globals) module env expressions heap values middle)
    (operation : primitive (.pop address) values middle = some (.ok value, finalHeap)) :
    Evaluates (globals := globals) module env (.call (.attribute (.name name) "pop") expressions)
      heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr (.name name) env, .methodReceiver "pop" expressions env :: stack, heap⟩)
    (by simp [step, lookup])
  apply Reaches.next (following := ⟨.value (.ref address), .methodReceiver "pop" expressions env :: stack, heap⟩)
    (by simp [step, lookup])
  apply Reaches.next (following := argumentsState (.pop address) env [] expressions stack heap)
    (by simp [step, run, bound])
  apply (arguments_reach arguments (.pop address) [] anchors stack).trans
  exact .next (by simp [step, result, run, operation]) .refl

theorem append (receiver : Evaluates (globals := globals) module env base heap (.ref address) middle)
    (found : middle[address]? = some (.list old))
    (item : Evaluates (globals := globals) module env expression middle value afterItem)
    (items : afterItem[address]? = some (.list current)) :
    Evaluates (globals := globals) module env (.call (.attribute base "append") [expression]) heap (.scalar .none)
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
theorem add (receiver : Evaluates (globals := globals) module env base heap (.ref address) middle)
    (found : middle[address]? = some (.set old))
    (item : Evaluates (globals := globals) module env expression middle (.scalar value) afterItem)
    (items : afterItem[address]? = some (.set current)) :
    Evaluates (globals := globals) module env (.call (.attribute base "add") [expression]) heap (.scalar .none)
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
    (heap : Heap) (value : Value) (finalHeap : Heap) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, Reaches (globals := globals) module anchors ⟨.block body env, stack, heap⟩ ⟨.value value, stack, finalHeap⟩

namespace BlockReturns

theorem return_value (evaluated : Evaluates (globals := globals) module env expression heap value finalHeap) :
    BlockReturns (globals := globals) module env (.return expression :: rest) heap value finalHeap :=
  fun anchors stack => .next rfl (evaluated anchors stack)

theorem assign (evaluated : Evaluates (globals := globals) module env expression heap value middle)
    (rest : BlockReturns (globals := globals) module (setLocal env name value) body middle answer finalHeap) :
    BlockReturns (globals := globals) module env (.assign [.name name] expression :: body) heap answer finalHeap :=
  fun anchors stack => .next rfl ((evaluated anchors _).trans (.next rfl (rest anchors stack)))

theorem unpack (targets : Calls.targetNames expressions = some names)
    (evaluated : Evaluates (globals := globals) module env expression heap value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, afterUnpack))
    (arity : names.length = items.length)
    (rest : BlockReturns (globals := globals) module (assignNames env names items) body afterUnpack answer finalHeap) :
    BlockReturns (globals := globals) module env (.assign [.tuple expressions] expression :: body) heap answer finalHeap := by
  intro anchors stack
  exact .next (following := ⟨.expr expression env, .unpack names body env :: stack, heap⟩)
    (by simp [step, targets]) ((evaluated anchors _).trans
    (.next (by simp [step, run, sequence, arity]) (rest anchors stack)))

/-- Subscription assignment evaluates the RHS before the receiver and index. -/
theorem setItem
    (ordinary : ∀ a b c, index ≠ .slice a b c)
    (rhs : Evaluates (globals := globals) module env expression heap value afterRhs)
    (target : Evaluates.Arguments (globals := globals) module env [base, index] afterRhs [receiver, subscript] afterTarget)
    (write : Mutable.setItem receiver subscript value afterTarget = some (.ok (.scalar .none), afterWrite))
    (rest : BlockReturns (globals := globals) module env body afterWrite answer finalHeap) :
    BlockReturns (globals := globals) module env (.assign [.subscript base index] expression :: body) heap answer finalHeap := by
  intro anchors stack
  have start : step (globals := globals) module anchors ⟨.block (.assign [.subscript base index] expression :: body) env, stack, heap⟩ =
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
    (rhs : Evaluates (globals := globals) module env expression heap value afterRhs)
    (target : Evaluates.Arguments (globals := globals) module env [base, lower.getD (.constant .none),
      upper.getD (.constant .none), stride.getD (.constant .none)] afterRhs
      [receiver, lowerValue, upperValue, strideValue] afterTarget)
    (write : Mutable.setSlice receiver lowerValue upperValue strideValue value afterTarget =
      some (.ok (.scalar .none), afterWrite))
    (rest : BlockReturns (globals := globals) module env body afterWrite answer finalHeap) :
    BlockReturns (globals := globals) module env (.assign [.subscript base (.slice lower upper stride)] expression :: body)
      heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (rhs anchors _).trans
  apply Reaches.next rfl
  apply (Evaluates.arguments_reach target (.setSlice value) [] anchors _).trans
  exact .next (following := ⟨.value (.scalar .none), .discard body env :: stack, afterWrite⟩)
    (by simp [step, result, run, primitive, write]) (.next rfl (rest anchors stack))

theorem augAssign (lookup : env name = some left)
    (evaluated : Evaluates (globals := globals) module env expression heap right middle)
    (operation : inplace op left right middle = some (.ok value, afterOperation))
    (rest : BlockReturns (globals := globals) module (setLocal env name value) body afterOperation answer finalHeap) :
    BlockReturns (globals := globals) module env (.augAssign (.name name) op expression :: body) heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (Evaluates.lookup (globals := globals) (module := module) (heap := heap) lookup anchors _).trans
  apply Reaches.next rfl
  apply (evaluated anchors _).trans
  exact .next (following := ⟨.value value, .assign name body env :: stack, afterOperation⟩)
    (by simp [step, result, run, operation]) (.next rfl (rest anchors stack))

theorem discard (evaluated : Evaluates (globals := globals) module env expression heap value middle)
    (rest : BlockReturns (globals := globals) module env body middle answer finalHeap) :
    BlockReturns (globals := globals) module env (.expr expression :: body) heap answer finalHeap :=
  fun anchors stack => .next rfl ((evaluated anchors _).trans (.next rfl (rest anchors stack)))

/-- Successful assertions retain condition effects and skip the message. -/
theorem assertion (evaluated : Evaluates (globals := globals) module env condition heap value middle)
    (truth : Mutable.truth value middle = some (.ok true, middle))
    (rest : BlockReturns (globals := globals) module env body middle answer finalHeap) :
    BlockReturns (globals := globals) module env (.assert condition message :: body) heap answer finalHeap := by
  intro anchors stack
  exact .next rfl ((evaluated anchors _).trans
    (.next (by simp [step, run, truth]) (rest anchors stack)))

theorem branch (evaluated : Evaluates (globals := globals) module env condition heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockReturns (globals := globals) module env ((if flag then yes else no) ++ body) middle answer finalHeap) :
    BlockReturns (globals := globals) module env (.ifThen condition yes no :: body) heap answer finalHeap := by
  intro anchors stack
  exact .next rfl ((evaluated anchors _).trans (.next (by simp [step, run, truth]) (rest anchors stack)))

theorem while_loop (evaluated : Evaluates (globals := globals) module env condition heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockReturns (globals := globals) module env
      ((if flag then body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)] else otherwise) ++ following)
      middle answer finalHeap) :
    BlockReturns (globals := globals) module env (.whileDo condition body otherwise :: following) heap answer finalHeap := by
  intro anchors stack
  exact .next rfl ((evaluated anchors _).trans (.next (by simp [step, run, truth]) (rest anchors stack)))

private theorem range_reach
    (h : Evaluates.Arguments (globals := globals) module env expressions heap values finalHeap) (done : List Value)
    (anchors : Nat) (stack : List Frame) :
    Reaches (globals := globals) module anchors (rangeState name env done expressions body otherwise following stack heap)
      ⟨.startRange name (done ++ values) body otherwise following env, stack, finalHeap⟩ := by
  induction h generalizing done with
  | nil => simp [rangeState]; exact .refl
  | @cons expression heap value middle expressions values finalHeap globals head tail ih =>
      apply (head _ _).trans
      refine .next rfl ?_
      simpa [List.append_assoc] using ih (done ++ [value])

theorem for_range (arguments : Evaluates.Arguments (globals := globals) module env expressions heap values middle)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (rest : BlockReturns (globals := globals) module env (.rangeStepLoop name start stop stride body otherwise :: following)
      middle answer finalHeap) :
    BlockReturns (globals := globals) module env (.forIn (.name name) (.call (.name "range") expressions) body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  exact .next rfl ((range_reach arguments [] anchors stack).trans
    (.next (by simp [step, bounds]) (rest anchors stack)))

/-- Evaluate a sequence expression once, then retain its object identity. -/
theorem for_sequence (ordinary : ∀ expressions, iterable ≠ .call (.name "range") expressions)
    (evaluated : Evaluates (globals := globals) module env iterable heap value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, middle))
    (rest : BlockReturns (globals := globals) module env
      (.sequenceStepLoop name (sequenceSource value) 0 body otherwise :: following) middle answer finalHeap) :
    BlockReturns (globals := globals) module env (.forIn (.name name) iterable body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  have start : step (globals := globals) module anchors ⟨.block (.forIn (.name name) iterable body otherwise :: following) env, stack, heap⟩ =
      .next ⟨.expr iterable env, .sequence name body otherwise following env :: stack, heap⟩ := by
    have notPermutations := evaluated.not_permutations
    cases iterable <;> simp_all [step]
  exact .next start ((evaluated anchors _).trans
    (.next (by simp [step, run, sequence]) (rest anchors stack)))

/-- Iteration reads the current sequence, so mutations in earlier iterations remain visible. -/
theorem sequence_step (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (rest : BlockReturns (globals := globals) module (setLocal env name value)
      (body ++ [Calls.loopContinuation body (.sequenceStepLoop name source (position + 1) body otherwise)] ++ following)
      heap answer finalHeap) :
    BlockReturns (globals := globals) module env (.sequenceStepLoop name source position body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, run, sequence, item]) (rest anchors stack)

theorem sequence_done (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (finished : items[position]? = none)
    (rest : BlockReturns (globals := globals) module env (otherwise ++ following) heap answer finalHeap) :
    BlockReturns (globals := globals) module env (.sequenceStepLoop name source position body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, run, sequence, finished]) (rest anchors stack)

theorem range_step (continues : Calls.rangeContinues next stop stride = true)
    (rest : BlockReturns (globals := globals) module (setLocal env name (.scalar (.int next)))
      (body ++ [Calls.loopContinuation body (.rangeStepLoop name (next + stride) stop stride body otherwise)] ++ following)
      heap answer finalHeap) :
    BlockReturns (globals := globals) module env (.rangeStepLoop name next stop stride body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, continues]) (rest anchors stack)

theorem range_done (finished : Calls.rangeContinues next stop stride = false)
    (rest : BlockReturns (globals := globals) module env (otherwise ++ following) heap answer finalHeap) :
    BlockReturns (globals := globals) module env (.rangeStepLoop name next stop stride body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, finished]) (rest anchors stack)

theorem loop_resume (rest : BlockReturns (globals := globals) module env (next :: following) heap answer finalHeap) :
    BlockReturns (globals := globals) module env (.loopResume next :: following) heap answer finalHeap :=
  fun anchors stack => .next rfl (rest anchors stack)

theorem break_loop (target : Calls.loopTarget body = some (next, following))
    (rest : BlockReturns (globals := globals) module env following heap answer finalHeap) :
    BlockReturns (globals := globals) module env (.breakLoop :: body) heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, target]) (rest anchors stack)

theorem continue_loop (target : Calls.loopTarget body = some (next, following))
    (rest : BlockReturns (globals := globals) module env (next :: following) heap answer finalHeap) :
    BlockReturns (globals := globals) module env (.continueLoop :: body) heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, target]) (rest anchors stack)

theorem function (found : findFunctionIn module.body name = some (args, body))
    (arguments : completeArguments args values = some completed)
    (evaluated : BlockReturns (globals := globals) module (functionEnv args body completed globals) (executableBody body) heap value finalHeap) :
    ReturnsValue (globals := globals) module name values heap value finalHeap := by
  intro anchors stack
  exact .next (by simp [step, found, arguments]) (evaluated anchors stack)

end BlockReturns

/-- Normal completion of a statement block, preserving any following statements
and caller continuation while exposing the updated locals and shared heap. -/
def BlockContinues (module : Module) (env : Env) (body : List Stmt)
    (heap : Heap) (finalEnv : Env) (finalHeap : Heap) (globals : Mutable.Globals := []) : Prop :=
  ∀ following anchors stack,
    Reaches (globals := globals) module anchors ⟨.block (body ++ following) env, stack, heap⟩
      ⟨.block following finalEnv, stack, finalHeap⟩

namespace BlockContinues

theorem nil : BlockContinues (globals := globals) module env [] heap env heap :=
  fun _ _ _ => .refl

theorem append (first : BlockContinues (globals := globals) module env body heap middleEnv middleHeap)
    (second : BlockContinues (globals := globals) module middleEnv rest middleHeap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env (body ++ rest) heap finalEnv finalHeap := by
  intro following anchors stack
  simpa only [List.append_assoc] using
    (first (rest ++ following) anchors stack).trans (second following anchors stack)

theorem assign (evaluated : Evaluates (globals := globals) module env expression heap value finalHeap) :
    BlockContinues (globals := globals) module env [.assign [.name name] expression] heap
      (setLocal env name value) finalHeap :=
  fun _ anchors _ => .next rfl ((evaluated anchors _).trans (.next rfl .refl))

theorem annAssign (evaluated : Evaluates (globals := globals) module env expression heap value finalHeap) :
    BlockContinues (globals := globals) module env [.annAssign (.name name) annotation (some expression)] heap
      (setLocal env name value) finalHeap :=
  fun _ anchors _ => .next rfl ((evaluated anchors _).trans (.next rfl .refl))

theorem annotation (annotation : Expr) : BlockContinues (globals := globals) module env [.annAssign (.name name) annotation none] heap env heap :=
  fun _ _ _ => .next rfl .refl

theorem unpack (targets : Calls.targetNames expressions = some names)
    (evaluated : Evaluates (globals := globals) module env expression heap value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, finalHeap))
    (arity : names.length = items.length) :
    BlockContinues (globals := globals) module env [.assign [.tuple expressions] expression] heap
      (assignNames env names items) finalHeap := by
  intro following anchors stack
  exact .next (following := ⟨.expr expression env, .unpack names following env :: stack, heap⟩)
    (by simp [step, targets]) ((evaluated anchors _).trans
    (.next (by simp [step, run, sequence, arity]) .refl))

/-- Augmented assignment exposes its updated local and heap to following statements. -/
theorem augAssign (lookup : env name = some left)
    (evaluated : Evaluates (globals := globals) module env expression heap right middle)
    (operation : inplace op left right middle = some (.ok value, finalHeap)) :
    BlockContinues (globals := globals) module env [.augAssign (.name name) op expression] heap
      (setLocal env name value) finalHeap := by
  intro following anchors stack
  apply Reaches.next rfl
  apply (Evaluates.lookup (globals := globals) (module := module) (heap := heap) lookup anchors _).trans
  apply Reaches.next rfl
  apply (evaluated anchors _).trans
  exact .next (following := ⟨.value value, .assign name following env :: stack, finalHeap⟩)
    (by simp [step, result, run, operation]) (.next rfl .refl)

/-- Subscription assignment evaluates the RHS before the receiver and index. -/
theorem setItem
    (ordinary : ∀ a b c, index ≠ .slice a b c)
    (rhs : Evaluates (globals := globals) module env expression heap value afterRhs)
    (target : Evaluates.Arguments (globals := globals) module env [base, index] afterRhs [receiver, subscript] afterTarget)
    (write : Mutable.setItem receiver subscript value afterTarget = some (.ok (.scalar .none), afterWrite)) :
    BlockContinues (globals := globals) module env [.assign [.subscript base index] expression] heap env afterWrite := by
  intro body anchors stack
  have start : step (globals := globals) module anchors ⟨.block (.assign [.subscript base index] expression :: body) env, stack, heap⟩ =
      .next ⟨.expr expression env, .assignItem base index body env :: stack, heap⟩ := by
    cases index <;> simp_all [step]
  apply Reaches.next start
  apply (rhs anchors _).trans
  apply Reaches.next rfl
  apply (Evaluates.arguments_reach target (.setItem value) [] anchors _).trans
  exact .next (following := ⟨.value (.scalar .none), .discard body env :: stack, afterWrite⟩)
    (by simp [step, result, run, primitive, write]) (.next rfl .refl)

/-- Augmented subscription saves the receiver and index, reads before the RHS,
and writes the in-place result back through the saved target. -/
theorem augItem
    (ordinary : ∀ a b c, index ≠ .slice a b c)
    (receiver : Evaluates (globals := globals) module env base heap target afterReceiver)
    (subscript : Evaluates (globals := globals) module env index afterReceiver key afterIndex)
    (read : Mutable.getItem target key afterIndex = some (.ok previous, afterRead))
    (rhs : Evaluates (globals := globals) module env expression afterRead right afterRhs)
    (operation : inplace op previous right afterRhs = some (.ok updated, afterOperation))
    (write : Mutable.setItem target key updated afterOperation = some (.ok (.scalar .none), finalHeap)) :
    BlockContinues (globals := globals) module env [.augAssign (.subscript base index) op expression]
      heap env finalHeap := by
  intro following anchors stack
  have start : step (globals := globals) module anchors
      ⟨.block (.augAssign (.subscript base index) op expression :: following) env, stack, heap⟩ =
      .next ⟨.expr base env, .augmentItemReceiver index op expression following env :: stack, heap⟩ := by
    cases index <;> simp_all [step]
  apply Reaches.next start
  apply (receiver anchors _).trans
  apply Reaches.next rfl
  apply (subscript anchors _).trans
  apply Reaches.next (following := ⟨.expr expression env,
    .binaryRight op previous true :: .writeItem target key following env :: stack, afterRead⟩)
    (by simp [step, run, read])
  apply (rhs anchors _).trans
  apply Reaches.next (following := ⟨.value updated, .writeItem target key following env :: stack, afterOperation⟩)
    (by simp [step, result, run, operation])
  apply Reaches.next (following := ⟨.value (.scalar .none), .discard following env :: stack, finalHeap⟩)
    (by simp [step, result, run, write])
  exact .next rfl .refl

/-- Slice bounds run left to right after the RHS and receiver; conversion follows. -/
theorem setSlice
    (rhs : Evaluates (globals := globals) module env expression heap value afterRhs)
    (target : Evaluates.Arguments (globals := globals) module env [base, lower.getD (.constant .none),
      upper.getD (.constant .none), stride.getD (.constant .none)] afterRhs
      [receiver, lowerValue, upperValue, strideValue] afterTarget)
    (write : Mutable.setSlice receiver lowerValue upperValue strideValue value afterTarget =
      some (.ok (.scalar .none), afterWrite)) :
    BlockContinues (globals := globals) module env [.assign [.subscript base (.slice lower upper stride)] expression]
      heap env afterWrite := by
  intro body anchors stack
  apply Reaches.next rfl
  apply (rhs anchors _).trans
  apply Reaches.next rfl
  apply (Evaluates.arguments_reach target (.setSlice value) [] anchors _).trans
  exact .next (following := ⟨.value (.scalar .none), .discard body env :: stack, afterWrite⟩)
    (by simp [step, result, run, primitive, write]) (.next rfl .refl)

theorem discard (evaluated : Evaluates (globals := globals) module env expression heap value finalHeap) :
    BlockContinues (globals := globals) module env [.expr expression] heap env finalHeap :=
  fun _ anchors _ => .next rfl ((evaluated anchors _).trans (.next rfl .refl))

theorem branch (evaluated : Evaluates (globals := globals) module env condition heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (body : BlockContinues (globals := globals) module env (if flag then yes else no) middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.ifThen condition yes no] heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next rfl ((evaluated anchors _).trans
    (.next (by simp [step, run, truth]) (body following anchors stack)))

/-- A while loop exposes its final locals and heap to the following block. -/
theorem while_loop (evaluated : Evaluates (globals := globals) module env condition heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockContinues (globals := globals) module env
      (if flag then body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)] else otherwise)
      middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.whileDo condition body otherwise] heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next rfl ((evaluated anchors _).trans
    (.next (by simp [step, run, truth]) (rest following anchors stack)))

theorem for_range (arguments : Evaluates.Arguments (globals := globals) module env expressions heap values middle)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (executed : BlockContinues (globals := globals) module env [.rangeStepLoop name start stop stride body otherwise]
      middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.forIn (.name name) (.call (.name "range") expressions) body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next rfl ((BlockReturns.range_reach arguments [] anchors stack).trans
    (.next (by simp [step, bounds]) (executed following anchors stack)))

theorem for_sequence (ordinary : ∀ expressions, iterable ≠ .call (.name "range") expressions)
    (evaluated : Evaluates (globals := globals) module env iterable heap value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, middle))
    (rest : BlockContinues (globals := globals) module env
      [.sequenceStepLoop name (sequenceSource value) 0 body otherwise] middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.forIn (.name name) iterable body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  have start : step (globals := globals) module anchors ⟨.block (.forIn (.name name) iterable body otherwise :: following) env, stack, heap⟩ =
      .next ⟨.expr iterable env, .sequence name body otherwise following env :: stack, heap⟩ := by
    have notPermutations := evaluated.not_permutations
    cases iterable <;> simp_all [step]
  exact .next start ((evaluated anchors _).trans
    (.next (by simp [step, run, sequence]) (rest following anchors stack)))

theorem sequence_step (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (rest : BlockContinues (globals := globals) module (setLocal env name value)
      (body ++ [Calls.loopContinuation body (.sequenceStepLoop name source (position + 1) body otherwise)])
      heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.sequenceStepLoop name source position body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  refine .next ?_ (rest following anchors stack)
  simp [step, run, sequence, item, List.append_assoc]

theorem sequence_done (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (finished : items[position]? = none)
    (rest : BlockContinues (globals := globals) module env otherwise heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.sequenceStepLoop name source position body otherwise]
      heap finalEnv finalHeap :=
  fun following anchors stack => .next (by simp [step, run, sequence, finished]) (rest following anchors stack)

/-- The outer sequence is evaluated once; each item is unpacked just before its body. -/
theorem for_unpack
    (ordinary : ∀ expressions, iterable ≠ .call (.name "enumerate") expressions)
    (targets : Calls.targetNames expressions = some names)
    (evaluated : Evaluates (globals := globals) module env iterable heap value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, middle))
    (rest : BlockContinues (globals := globals) module env
      [.unpackStepLoop names (sequenceSource value) 0 body otherwise] middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.forIn (.tuple expressions) iterable body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  have start : step (globals := globals) module anchors
      ⟨.block (.forIn (.tuple expressions) iterable body otherwise :: following) env, stack, heap⟩ =
      .next ⟨.expr iterable env, .unpackSequence names body otherwise following env :: stack, heap⟩ := by
    have notPermutations := evaluated.not_permutations
    cases iterable <;> simp_all [step]
  exact .next start ((evaluated anchors _).trans
    (.next (by simp [step, run, sequence]) (rest following anchors stack)))

/-- Validate the entire item before assigning names left to right, preserving aliases. -/
theorem unpack_step
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (fields : Mutable.sequence value heap = some (.ok values, heap))
    (arity : names.length = values.length)
    (rest : BlockContinues (globals := globals) module (assignNames env names values)
      (body ++ [Calls.loopContinuation body (.unpackStepLoop names source (position + 1) body otherwise)])
      heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.unpackStepLoop names source position body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  refine .next ?_ (rest following anchors stack)
  simp [step, run, sequence, item, fields, arity, List.append_assoc]

theorem unpack_done
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (finished : items[position]? = none)
    (rest : BlockContinues (globals := globals) module env otherwise heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.unpackStepLoop names source position body otherwise]
      heap finalEnv finalHeap :=
  fun following anchors stack => .next (by simp [step, run, sequence, finished]) (rest following anchors stack)

/-- Evaluate the iterable and explicit start before constructing the iterator. -/
theorem for_enumerate_start
    (iterable : Evaluates (globals := globals) module env expression heap source afterSource)
    (start : Evaluates (globals := globals) module env startExpression afterSource startValue middle)
    (counter : enumerateStart startValue middle = some (.ok initial, middle))
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (rest : BlockContinues (globals := globals) module env
      [.enumerateStepLoop index name (sequenceSource source) 0 initial body otherwise] middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env
      [.forIn (.tuple [.name index, .name name]) (.call (.name "enumerate") [expression, startExpression]) body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next rfl ((iterable anchors _).trans (.next rfl ((start anchors _).trans
    (.next (by simp [step, run, counter, sequence]) (rest following anchors stack)))))

theorem for_enumerate
    (iterable : Evaluates (globals := globals) module env expression heap source middle)
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (rest : BlockContinues (globals := globals) module env
      [.enumerateStepLoop index name (sequenceSource source) 0 0 body otherwise] middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env
      [.forIn (.tuple [.name index, .name name]) (.call (.name "enumerate") [expression]) body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next rfl ((iterable anchors _).trans (.next rfl (.next rfl
    (.next (by simp [step, run, enumerateStart, sequence]) (rest following anchors stack)))))

/-- The hidden pair cannot escape immediate unpacking; its two bindings are ordered. -/
theorem enumerate_step
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (rest : BlockContinues (globals := globals) module (setLocal (setLocal env index (.scalar (.int counter))) name value)
      (body ++ [Calls.loopContinuation body
        (.enumerateStepLoop index name source (position + 1) (counter + 1) body otherwise)])
      heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.enumerateStepLoop index name source position counter body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  refine .next ?_ (rest following anchors stack)
  simp [step, run, sequence, item, List.append_assoc]

theorem enumerate_done
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (finished : items[position]? = none)
    (rest : BlockContinues (globals := globals) module env otherwise heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.enumerateStepLoop index name source position counter body otherwise]
      heap finalEnv finalHeap :=
  fun following anchors stack => .next (by simp [step, run, sequence, finished]) (rest following anchors stack)

theorem range_step (continues : Calls.rangeContinues next stop stride = true)
    (rest : BlockContinues (globals := globals) module (setLocal env name (.scalar (.int next)))
      (body ++ [Calls.loopContinuation body (.rangeStepLoop name (next + stride) stop stride body otherwise)])
      heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.rangeStepLoop name next stop stride body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  refine .next ?_ (rest following anchors stack)
  simp [step, continues, List.append_assoc]

theorem range_done (finished : Calls.rangeContinues next stop stride = false)
    (rest : BlockContinues (globals := globals) module env otherwise heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.rangeStepLoop name next stop stride body otherwise]
      heap finalEnv finalHeap :=
  fun following anchors stack => .next (by simp [step, finished]) (rest following anchors stack)

theorem loop_resume (rest : BlockContinues (globals := globals) module env [next] heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.loopResume next] heap finalEnv finalHeap :=
  fun following anchors stack => .next rfl (rest following anchors stack)

theorem returns (first : BlockContinues (globals := globals) module env body heap middleEnv middleHeap)
    (rest : BlockReturns (globals := globals) module middleEnv following middleHeap answer finalHeap) :
    BlockReturns (globals := globals) module env (body ++ following) heap answer finalHeap :=
  fun anchors stack => (first following anchors stack).trans (rest anchors stack)

end BlockContinues

/-- Emission keeps the current comprehension locals and appends the actual value,
including shared references, after evaluating the element's effects. -/
theorem BlockContinues.comprehension_append
    (evaluated : Evaluates (globals := globals) module env expression heap value middle)
    (found : middle[address]? = some (.list items)) :
    BlockContinues (globals := globals) module env [.comprehensionAppend address expression] heap env
      (middle.set address (.list (items ++ [value]))) := by
  intro following anchors stack
  apply Reaches.next rfl
  apply (Evaluates.arguments_reach (.cons evaluated .nil) (.append address) [] anchors _).trans
  exact .next (following := ⟨.value (.scalar .none), .discard following env :: stack,
    middle.set address (.list (items ++ [value]))⟩)
    (by simp [step, result, run, primitive, Mutable.appendItem, found, Except.map])
    (.next rfl .refl)

/-- Insert after evaluating element effects, retaining the first equal representative. -/
theorem BlockContinues.comprehension_add
    (evaluated : Evaluates (globals := globals) module env expression heap (.scalar value) middle)
    (found : middle[address]? = some (.set items)) :
    BlockContinues (globals := globals) module env [.comprehensionAdd address expression] heap env
      (middle.set address (.set (ScalarSet.insert items value))) := by
  intro following anchors stack
  apply Reaches.next rfl
  apply (Evaluates.arguments_reach (.cons evaluated .nil) (.add address) [] anchors _).trans
  exact .next (following := ⟨.value (.scalar .none), .discard following env :: stack,
    middle.set address (.set (ScalarSet.insert items value))⟩)
    (by simp [step, result, run, primitive, Mutable.addItem, found, Except.map])
    (.next rfl .refl)

/-- Prove a range comprehension by composing ordinary loop proofs. Only its
first range arguments use the enclosing scope. -/
theorem Evaluates.list_comp_range
    (arguments : Arguments (globals := globals) module env expressions heap values middle)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (executed : BlockContinues (globals := globals) module
      (comprehensionEnv env ((name, .call (.name "range") expressions, filters) :: generators))
      [.rangeStepLoop name start stop stride
        (comprehensionFilters filters (comprehensionBody middle.length element generators)) []]
      (middle ++ [.list []]) finalEnv finalHeap) :
    Evaluates (globals := globals) module env
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
    (evaluated : Evaluates (globals := globals) module env iterable heap value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, middle))
    (executed : BlockContinues (globals := globals) module
      (comprehensionEnv env ((name, iterable, filters) :: generators))
      [.sequenceStepLoop name (sequenceSource value) 0
        (comprehensionFilters filters (comprehensionBody middle.length element generators)) []]
      (middle ++ [.list []]) finalEnv finalHeap) :
    Evaluates (globals := globals) module env (.listComp element ((name, iterable, filters) :: generators))
      heap (.ref middle.length) finalHeap := by
  intro anchors stack
  have first : step (globals := globals) module anchors
      ⟨.expr (.listComp element ((name, iterable, filters) :: generators)) env, stack, heap⟩ =
      .next (argumentsState
        (.comprehension element ((name, iterable, filters) :: generators)
          (comprehensionEnv env ((name, iterable, filters) :: generators)))
        env [] [iterable] stack heap) := by
    have notPermutations := evaluated.not_permutations
    cases iterable <;> simp_all [step]
  apply Reaches.next first
  apply (arguments_reach (.cons evaluated .nil) _ [] anchors stack).trans
  refine .next ?_
    ((executed [] anchors (.comprehensionResult middle.length :: stack)).trans
      (.next rfl (.next rfl .refl)))
  cases iterable <;> simp_all [step, comprehensionStart, run]

/-- Sequence extrema preserve both retained item identities and every key's heap effects. -/
def ExtremumReturns (module : Module) (cursor : SequenceExtremum) (position : Nat)
    (best : Option (Value × Value)) (heap : Heap) (value : Value) (finalHeap : Heap)
    (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, Reaches (globals := globals) module anchors
    ⟨.extremumLoop cursor position best, stack, heap⟩ ⟨.value value, stack, finalHeap⟩

namespace ExtremumReturns

theorem done (exhausted : extremumItem cursor.source position heap = some (.ok none, heap)) :
    ExtremumReturns (globals := globals) module cursor position (some (winner, score)) heap winner heap := by
  intro anchors stack
  exact .next (by simp [step, run, exhausted]) .refl

theorem next (read : extremumItem cursor.source position heap = some (.ok (some candidate), heap))
    (key : Evaluates (globals := globals) module (setLocal cursor.env cursor.parameter candidate)
      cursor.key heap score afterKey)
    (selected : cursor.choose candidate score best afterKey = some (.ok updated, afterSelection))
    (rest : ExtremumReturns (globals := globals) module cursor (position + 1) (some updated)
      afterSelection value finalHeap) :
    ExtremumReturns (globals := globals) module cursor position best heap value finalHeap := by
  intro anchors stack
  exact .next (by simp [step, run, read]) ((key anchors (.extremumKey cursor position candidate best :: stack)).trans
    (.next (by simp [step, run, selected]) (rest anchors stack)))

end ExtremumReturns

theorem Evaluates.extremum_sequence
    (iterable : Evaluates (globals := globals) module env expression heap source middle)
    (acquired : Mutable.sequence source middle = some (.ok items, middle))
    (rest : ExtremumReturns (globals := globals) module ⟨maximum, source, parameter, key, env⟩ 0 none
      middle value finalHeap) :
    Evaluates (globals := globals) module env (.extremumSequence maximum expression parameter key)
      heap value finalHeap := by
  intro anchors stack
  exact .next rfl ((iterable anchors (.extremumSource maximum parameter key env :: stack)).trans
    (.next (by simp [step, run, acquired]) (rest anchors stack)))

end FormalSW.PyAst.HeapCalls

namespace FormalSW.PyAst.Mutable.Call

/-- Heap execution coverage includes exceptional completion with its final heap. -/
def Supported (call : Call) : Prop := call.execution.Supported

theorem Returns.supported {call : Call} (h : call.Returns) : call.Supported := by
  obtain ⟨value, globals, heap, anchors, run⟩ := h
  exact Execution.supported_of_finishes run

end FormalSW.PyAst.Mutable.Call
