import lang.py.FormalSW.MutableGlobals
import lang.py.FormalSW.Linking

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
                    | some (.list _) => Mutable.error "TypeError"
                    | none => Mutable.unsupported
                | _ => Mutable.error "TypeError"
              modify fun heap => heap.set address (.bytearray (bytes ++ more))
              return left
          | _ => Mutable.binary op left right

inductive Operation where
  | call (name : String)
  | list
  | subscript
  | slice
  | setItem (replacement : Value)
  | setSlice (replacement : Value)
  | append (address : Nat)
  | builtin (name : Builtin)
  | reversedList

inductive Frame where
  | binaryLeft (op : BinOp) (right : Expr) (env : Env) (inPlace : Bool)
  | binaryRight (op : BinOp) (left : Value) (inPlace : Bool)
  | compareLeft (op : CmpOp) (right : Expr) (env : Env)
  | compareRight (op : CmpOp) (left : Value)
  | unary (op : UnaryOp)
  | boolean (op : BoolOp) (rest : List Expr) (env : Env)
  | conditional (yes no : Expr) (env : Env)
  | arguments (operation : Operation) (done : List Value) (rest : List Expr) (env : Env)
  /-- Resolve the bound method before evaluating its argument. -/
  | appendReceiver (item : Expr) (env : Env)
  | assign (name : String) (rest : List Stmt) (env : Env)
  | branch (yes no rest : List Stmt) (env : Env)
  | discard (rest : List Stmt) (env : Env)
  | assertion (message : Option Expr) (rest : List Stmt) (env : Env)
  | assertionMessage
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

def primitive : Operation → List Value → Eval Value
  | .list, values => Mutable.allocate values
  | .reversedList, [value] => do
      Mutable.allocate (← Mutable.sequence value).reverse
  | .subscript, [base, index] => Mutable.getItem base index
  | .slice, [base, lower, upper, stride] => Mutable.getSlice base lower upper stride
  | .setItem replacement, [base, index] => Mutable.setItem base index replacement
  | .setSlice replacement, [base, lower, upper, stride] => Mutable.setSlice base lower upper stride replacement
  | .append address, [value] => Mutable.appendItem address value
  | .builtin .bytearray, values => Mutable.bytearray values
  | .builtin .intBitLength, [.scalar value] => scalarResult (some (Math.bitLengthCall value))
  | .builtin .intBitLength, [.ref _] => Mutable.error "AttributeError"
  | .builtin .str, values => do
      let values ← values.mapM fun value => match value with
        | .scalar value => pure value
        | .ref _ => Mutable.unsupported
      scalarResult (some (Strings.str values))
  | .builtin .max, values => do
      let values ← values.mapM fun value => match value with
        | .scalar value => pure value
        | .ref _ => Mutable.unsupported
      scalarResult (Calls.positionalMaximum values)
  | _, _ => Mutable.unsupported

def library (module : Module) (name : String) (values : List Value) : Eval Value := do
  let some function := libraryFunction module name | Mutable.unsupported
  let scalars ← values.mapM fun value => match value with
    | .scalar scalar => pure scalar
    | .ref _ => Mutable.error "TypeError"
  scalarResult (some (function scalars))

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
      | none => result anchors heap (library module name values) stack
  | .operation operation values => result anchors heap (primitive operation values) stack
  | .expr expression env =>
      match expression with
      | .constant value => .next ⟨.value (.scalar value), stack, heap⟩
      | .name name => match env name with
          | some value => .next ⟨.value value, stack, heap⟩
          | none => done anchors heap (.error { typeName := "UnboundLocalError", args := [] })
      | .binOp a op b => .next ⟨.expr a env, .binaryLeft op b env false :: stack, heap⟩
      | .unaryOp op expression => .next ⟨.expr expression env, .unary op :: stack, heap⟩
      | .compare a [(op, b)] => .next ⟨.expr a env, .compareLeft op b env :: stack, heap⟩
      | .boolOp op (first :: rest) => .next ⟨.expr first env, .boolean op rest env :: stack, heap⟩
      | .ifExp test yes no => .next ⟨.expr test env, .conditional yes no env :: stack, heap⟩
      | .list expressions => .next (argumentsState .list env [] expressions stack heap)
      | .reversedList expression => .next (argumentsState .reversedList env [] [expression] stack heap)
      | .subscript base (.slice lower upper stride) =>
          .next (argumentsState .slice env [] [base, lower.getD (.constant .none),
            upper.getD (.constant .none), stride.getD (.constant .none)] stack heap)
      | .subscript base index => .next (argumentsState .subscript env [] [base, index] stack heap)
      | .builtinCall name expressions => .next (argumentsState (.builtin name) env [] expressions stack heap)
      | .call (.name name) expressions => .next (argumentsState (.call name) env [] expressions stack heap)
      | .call (.attribute base "append") [item] => .next ⟨.expr base env, .appendReceiver item env :: stack, heap⟩
      | .call (.attribute (.name name) field) args =>
          .next (argumentsState (.call (name ++ "." ++ field)) env [] args stack heap)
      | _ => .unsupported
  | .block body env =>
      match body with
      | [] => .next ⟨.value (.scalar .none), stack, heap⟩
      | .return expression :: _ => .next ⟨.expr expression env, stack, heap⟩
      | .assign [.subscript base (.slice lower upper stride)] expression :: rest =>
          .next ⟨.expr expression env, .assignSlice base (lower.getD (.constant .none))
            (upper.getD (.constant .none)) (stride.getD (.constant .none)) rest env :: stack, heap⟩
      | .assign [.subscript base index] expression :: rest =>
          .next ⟨.expr expression env, .assignItem base index rest env :: stack, heap⟩
      | .assign [.name name] expression :: rest => .next ⟨.expr expression env, .assign name rest env :: stack, heap⟩
      | .augAssign (.name name) op expression :: rest =>
          .next ⟨.expr (.name name) env, .binaryLeft op expression env true :: .assign name rest env :: stack, heap⟩
      | .assert condition message :: rest =>
          .next ⟨.expr condition env, .assertion message rest env :: stack, heap⟩
      | .ifThen condition yes no :: rest => .next ⟨.expr condition env, .branch yes no rest env :: stack, heap⟩
      | .whileDo condition body otherwise :: rest =>
          .next ⟨.expr condition env,
            .branch (body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)]) otherwise rest env :: stack, heap⟩
      | .forIn (.name name) (.call (.name "range") expressions) body otherwise :: rest =>
          .next (rangeState name env [] expressions body otherwise rest stack heap)
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
      | _ => .unsupported
  | .value value =>
      match stack with
      | [] => done anchors heap (.ok value)
      | frame :: stack => match frame with
          | .binaryLeft op right env inPlace => .next ⟨.expr right env, .binaryRight op value inPlace :: stack, heap⟩
          | .binaryRight op left inPlace =>
              result anchors heap (if inPlace then inplace op left value else Mutable.binary op left value) stack
          | .compareLeft op right env => .next ⟨.expr right env, .compareRight op value :: stack, heap⟩
          | .compareRight op left => result anchors heap (compare op left value) stack
          | .unary op => result anchors heap (unary op value) stack
          | .boolean op rest env => run anchors heap (Mutable.truth value) fun truth heap =>
              if (match op with | .and => !truth | .or => truth) then .next ⟨.value value, stack, heap⟩
              else match rest with
                | [] => .next ⟨.value value, stack, heap⟩
                | first :: rest => .next ⟨.expr first env, .boolean op rest env :: stack, heap⟩
          | .conditional yes no env => run anchors heap (Mutable.truth value) fun truth heap =>
              .next ⟨.expr (if truth then yes else no) env, stack, heap⟩
          | .arguments operation done rest env => .next (argumentsState operation env (done ++ [value]) rest stack heap)
          | .appendReceiver item env => match value with
              | .scalar _ => done anchors heap (.error { typeName := "AttributeError", args := [] })
              | .ref address => run anchors heap (Mutable.appendReceiver value) fun _ heap =>
                  .next (argumentsState (.append address) env [] [item] stack heap)
          | .assignItem base index rest env =>
              .next (argumentsState (.setItem value) env [] [base, index] (.discard rest env :: stack) heap)
          | .assignSlice base lower upper stride rest env =>
              .next (argumentsState (.setSlice value) env [] [base, lower, upper, stride]
                (.discard rest env :: stack) heap)
          | .assign name rest env => .next ⟨.block rest (setLocal env name value), stack, heap⟩
          | .branch yes no rest env => run anchors heap (Mutable.truth value) fun truth heap =>
              .next ⟨.block ((if truth then yes else no) ++ rest) env, stack, heap⟩
          | .assertion message rest env => run anchors heap (Mutable.truth value) fun truth heap =>
              if truth then .next ⟨.block rest env, stack, heap⟩
              else match message with
                | none => done anchors heap (.error { typeName := "AssertionError", args := [] })
                | some expression => .next ⟨.expr expression env, .assertionMessage :: stack, heap⟩
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

/-- Imported helpers retain their checked bodies and share the caller's heap. -/
theorem step_extend (extension : Calls.Extends target source) (state : State)
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
              | none => simp [step, found, library, imported, result, run, Mutable.unsupported] at supported
              | some function =>
                  obtain ⟨absent, same⟩ := extension.libraryFunction_eq found imported
                  simp only [step, found, absent, library, imported, same]
          | some declaration =>
              rcases declaration with ⟨args, body⟩
              simp only [step, found, extension.functions name args body found]
      | list | subscript | slice | setItem _ | setSlice _ | append _ | builtin _ | reversedList => rfl
  | expr _ _ | block _ _ | value _ | startRange _ _ _ _ _ _ => rfl

theorem Reaches.extend (h : Reaches source anchors initial final) (extension : Calls.Extends target source) :
    Reaches target anchors initial final := by
  induction h with
  | refl => exact .refl
  | next transition _ ih =>
      apply Reaches.next _ ih
      rw [step_extend extension _ (by simp [transition])]
      exact transition

theorem ReturnsValue.extend (h : ReturnsValue source name values heap value finalHeap)
    (extension : Calls.Extends target source) : ReturnsValue target name values heap value finalHeap :=
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

theorem compare (left : Evaluates module env a heap av middle)
    (right : Evaluates module env b middle bv afterRight)
    (operation : HeapCalls.compare op av bv afterRight = some (.ok value, finalHeap)) :
    Evaluates module env (.compare a [(op, b)]) heap value finalHeap := by
  intro anchors stack
  exact .next rfl ((left _ _).trans (.next rfl ((right _ _).trans
    (.next (by simp [step, result, run, operation]) .refl))))

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

private theorem arguments_reach (h : Arguments module env expressions heap values finalHeap)
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
  apply call arguments
  intro anchors stack
  exact .next (by simp [step, absent, result, run, operation]) .refl

theorem qualified_call (notAppend : field ≠ "append")
    (arguments : Arguments module env expressions heap values middle)
    (callee : ReturnsValue module (alias ++ "." ++ field) values middle value finalHeap) :
    Evaluates module env (.call (.attribute (.name alias) field) expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := argumentsState (.call (alias ++ "." ++ field)) env [] expressions stack heap)
    (by simp [step, notAppend])
  exact (arguments_reach arguments (.call (alias ++ "." ++ field)) [] anchors stack).trans (callee anchors stack)

theorem list (arguments : Arguments module env expressions heap values finalHeap) :
    Evaluates module env (.list expressions) heap (.ref finalHeap.length) (finalHeap ++ [.list values]) := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments .list [] anchors stack).trans
  exact .next (by simp [step, result, run, primitive, Mutable.allocate, Except.map]) .refl

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

theorem for_range (arguments : Evaluates.Arguments module env expressions heap values middle)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (executed : BlockContinues module env [.rangeStepLoop name start stop stride body otherwise]
      middle finalEnv finalHeap) :
    BlockContinues module env [.forIn (.name name) (.call (.name "range") expressions) body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next rfl ((BlockReturns.range_reach arguments [] anchors stack).trans
    (.next (by simp [step, bounds]) (executed following anchors stack)))

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
end FormalSW.PyAst.HeapCalls

namespace FormalSW.PyAst.Mutable.Call

/-- Heap execution coverage includes exceptional completion with its final heap. -/
def Supported (call : Call) : Prop := call.execution.Supported

theorem Returns.supported {call : Call} (h : call.Returns) : call.Supported := by
  obtain ⟨value, globals, heap, anchors, run⟩ := h
  exact Execution.supported_of_finishes run

end FormalSW.PyAst.Mutable.Call
