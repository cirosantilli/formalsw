import lang.py.FormalSW.Globals
import lang.py.FormalSW.GraphEquivalence
import lang.py.builtin.type.bytearray
import lang.py.FormalSW.Strings

namespace FormalSW.PyAst.Mutable

/-- References are shared by arguments, globals, locals, and returned values. -/
inductive Value where
  | scalar (value : Constant)
  | ref (address : Nat)
deriving Repr, DecidableEq

/-- Mutable objects have stable addresses and retain their runtime type. -/
inductive Object where
  | list (items : List Value)
  | bytearray (bytes : List UInt8)
deriving Repr, DecidableEq

abbrev Heap := List Object
abbrev Globals := List (String × Value)
abbrev Env := String → Option Value

def Value.edge : Value → Graph.Edge
  | .scalar c => .scalar c
  | .ref n => .ref n

def Value.HasType (heap : Heap) (value : Value) (kind : String) : Prop :=
  match value with
  | .scalar (.int _) => kind = "int"
  | .scalar (.string _) => kind = "str"
  | .scalar (.bytes _) => kind = "bytes"
  | .scalar (.bool _) => kind = "bool"
  | .scalar .none => kind = "None"
  | .ref address => if kind = "bytearray" then
      ∃ bytes, heap[address]? = some (.bytearray bytes)
    else ∃ items, heap[address]? = some (.list items) ∧
      (kind = "list" ∨ ∃ elementKind, kind = "list[" ++ elementKind ++ "]" ∧
        ∀ item ∈ items, match item with
          | .scalar (.int _) => elementKind = "int"
          | .scalar (.string _) => elementKind = "str"
          | .scalar (.bool _) => elementKind = "bool"
          | _ => False)

/-- Every reference points into the heap; cycles and sharing are permitted. -/
def Heap.Valid (heap : Heap) : Prop :=
  ∀ object ∈ heap, match object with
    | .bytearray _ => True
    | .list items => ∀ value ∈ items, match value with
        | .scalar _ => True
        | .ref address => address < heap.length

structure Completion where
  outcome : Except ExceptionObject Value
  globals : Globals
  heap : Heap
  /-- Entry objects remain observable to callers, even after global rebinding. -/
  anchors : Nat
deriving Repr, DecidableEq

def Completion.snapshot (c : Completion) : Data :=
  let result := match c.outcome with | .ok v => [v.edge] | .error _ => []
  (Graph.Heap.mk ((List.range c.anchors).map Graph.Edge.ref ++
    c.globals.map (fun (_, v) => v.edge) ++ result)
    (c.heap.map fun object => match object with
      | .list items => ⟨.list, [], items.map Value.edge⟩
      | .bytearray bytes => ⟨.bytearray, [], bytes.map (fun byte => .scalar (.int byte.toNat))⟩)).encode

/-- Exact identical states are a fast path. Otherwise compare the rooted object
 graph using the interpreted Python comparison, preserving aliases and cycles. -/
def Completion.Equivalent (a b : Completion) : Prop :=
  a = b ∨ (a.anchors = b.anchors ∧ a.globals.map Prod.fst = b.globals.map Prod.fst ∧
    (match a.outcome, b.outcome with
      | .ok _, .ok _ => True
      | .error x, .error y => x = y
      | _, _ => False) ∧ Graph.Equivalent a.snapshot b.snapshot)

structure Call where
  execution : Execution Completion

namespace Call

def Finishes (call : Call) (result : Completion) : Prop :=
  PyAst.Finishes call.execution.step call.execution.initial (.ok result)
def Returns (call : Call) : Prop := ∃ v g h a, call.Finishes ⟨.ok v, g, h, a⟩
def Throws (call : Call) : Prop := ∃ e g h a, call.Finishes ⟨.error e, g, h, a⟩
def Halts (call : Call) : Prop := ∃ result, call.Finishes result
def Diverges (call : Call) : Prop := call.execution.Diverges
def Equiv (a b : Call) : Prop :=
  (∀ x, a.Finishes x → ∃ y, b.Finishes y ∧ x.Equivalent y) ∧
  (∀ y, b.Finishes y → ∃ x, a.Finishes x ∧ x.Equivalent y)
def EquivReturn (a b : Call) : Prop :=
  ∀ v g h n w j k m, a.Finishes ⟨.ok v, g, h, n⟩ → b.Finishes ⟨.ok w, j, k, m⟩ →
    Completion.Equivalent ⟨.ok v, g, h, n⟩ ⟨.ok w, j, k, m⟩
def ReturnType (call : Call) (kind : String) : Prop :=
  call.Throws ∨ ∃ v g h a, call.Finishes ⟨.ok v, g, h, a⟩ ∧ v.HasType h kind

theorem finishes_of_observe {call : Call}
    (h : call.execution.observe fuel = .done (.ok result)) : call.Finishes result :=
  Execution.finishes_of_observe h

theorem unique {call : Call} (a : call.Finishes x) (b : call.Finishes y) : x = y :=
  Except.ok.inj (a.unique b)

theorem throws_halts {call : Call} (h : call.Throws) : call.Halts := by
  obtain ⟨e, g, h, a, done⟩ := h
  exact ⟨_, done⟩

theorem returns_iff_halts_not_throws (call : Call) :
    call.Returns ↔ call.Halts ∧ ¬ call.Throws := by
  constructor
  · rintro ⟨v, g, h, a, done⟩
    refine ⟨⟨_, done⟩, ?_⟩
    rintro ⟨e, j, k, m, thrown⟩
    have eq := unique done thrown
    cases eq
  · rintro ⟨⟨⟨outcome, g, h, a⟩, done⟩, noThrow⟩
    cases outcome with
    | ok v => exact ⟨v, g, h, a, done⟩
    | error e => exact False.elim (noThrow ⟨e, g, h, a, done⟩)

theorem equiv_of_finishes {a b : Call} (ha : a.Finishes x) (hb : b.Finishes y)
    (eq : x.Equivalent y) : a.Equiv b := by
  constructor
  · intro z hz
    cases unique hz ha
    exact ⟨y, hb, eq⟩
  · intro z hz
    cases unique hz hb
    exact ⟨x, ha, eq⟩

theorem Equiv.equivReturn {a b : Call} (eq : a.Equiv b) : a.EquivReturn b := by
  intro v g h n w j k m ha hb
  obtain ⟨result, done, same⟩ := eq.1 _ ha
  cases unique done hb
  exact same

theorem Equiv.returns_iff {a b : Call} (eq : a.Equiv b) : a.Returns ↔ b.Returns := by
  constructor
  · rintro ⟨v, g, h, n, done⟩
    obtain ⟨⟨outcome, j, k, m⟩, other, same⟩ := eq.1 _ done
    cases outcome with
    | ok w => exact ⟨w, j, k, m, other⟩
    | error e =>
      rcases same with impossible | ⟨_, _, impossible, _⟩ <;> cases impossible
  · rintro ⟨v, g, h, n, done⟩
    obtain ⟨⟨outcome, j, k, m⟩, other, same⟩ := eq.2 _ done
    cases outcome with
    | ok w => exact ⟨w, j, k, m, other⟩
    | error e =>
      rcases same with impossible | ⟨_, _, impossible, _⟩ <;> cases impossible

theorem Equiv.halts_iff {a b : Call} (eq : a.Equiv b) : a.Halts ↔ b.Halts := by
  constructor
  · rintro ⟨result, done⟩
    obtain ⟨_, done, _⟩ := eq.1 _ done
    exact ⟨_, done⟩
  · rintro ⟨result, done⟩
    obtain ⟨_, done, _⟩ := eq.2 _ done
    exact ⟨_, done⟩

theorem diverges_not_halts {call : Call} (h : call.Diverges) : ¬ call.Halts := by
  rintro ⟨result, done⟩
  exact Execution.diverges_not_halts h ⟨.ok result, done⟩

end Call

/-- Exceptions retain the heap reached while evaluating the expression. -/
abbrev Eval := ExceptT ExceptionObject (StateT Heap Option)

@[simp] theorem eval_pure (value : α) (heap : Heap) :
    (pure value : Eval α) heap = some (.ok value, heap) := rfl

@[simp] theorem eval_bind (action : Eval α) (next : α → Eval β) (heap : Heap) :
    (action >>= next) heap = (do
      let (outcome, heap) ← action heap
      match outcome with
      | .error e => some (.error e, heap)
      | .ok v => next v heap) := by
  change (action heap >>= fun (result, heap) => ExceptT.bindCont next result heap) = _
  cases h : action heap with
  | none => rfl
  | some pair => rcases pair with ⟨result, heap⟩; cases result <;> rfl

@[simp] theorem eval_get (heap : Heap) : (get : Eval Heap) heap = some (.ok heap, heap) := rfl
@[simp] theorem eval_set (a b : Heap) : (set a : Eval PUnit) b = some (.ok ⟨⟩, a) := rfl
@[simp] theorem eval_modify (f : Heap → Heap) (heap : Heap) :
    (modify f : Eval PUnit) heap = some (.ok ⟨⟩, f heap) := rfl
@[simp] theorem eval_map (f : α → β) (action : Eval α) (heap : Heap) :
    (f <$> action) heap = (do
      let (outcome, heap) ← action heap
      some (outcome.map f, heap)) := by
  change (action >>= fun v => pure (f v)) heap = _
  rw [eval_bind]
  cases h : action heap with
  | none => rfl
  | some pair => rcases pair with ⟨result, heap⟩; cases result <;> rfl
@[simp] theorem eval_throw (e : ExceptionObject) (heap : Heap) :
    (throw e : Eval α) heap = some (.error e, heap) := rfl

def unsupported : Eval α := fun _ => none

def error (name : String) : Eval α := throw { typeName := name, args := [] }

def allocate (items : List Value) : Eval Value := do
  let heap ← get
  set (heap ++ [.list items])
  return .ref heap.length

/-- A buffer owns bytes, never references to other heap objects. -/
def allocateBuffer (bytes : List UInt8) : Eval Value := do
  let heap ← get
  set (heap ++ [.bytearray bytes])
  return .ref heap.length

def integer : Value → Eval Int
  | .scalar (.int n) => pure n
  | .scalar (.bool b) => pure (if b then 1 else 0)
  | _ => error "TypeError"

def byte (value : Value) : Eval UInt8 := do
  let n ← integer value
  if 0 ≤ n ∧ n < 256 then return UInt8.ofNat n.toNat
  else error "ValueError"

/-- Convert an existing buffer or iterable of integers; a bare size is not iterable. -/
def byteValues : Value → Eval (List UInt8)
  | .scalar (.bytes bytes) => pure bytes
  | .ref address => do
      match (← get)[address]? with
      | some (.bytearray bytes) => return bytes
      | some (.list items) => items.mapM byte
      | none => unsupported
  | _ => error "TypeError"

def bytearray : List Value → Eval Value
  | [] => allocateBuffer []
  | [.scalar (.int n)] =>
      if n < 0 then error "ValueError" else allocateBuffer (List.replicate n.toNat 0)
  | [.scalar (.bool b)] => allocateBuffer (if b then [0] else [])
  | [value] => do allocateBuffer (← byteValues value)
  | _ => error "TypeError"

def array (value : Value) : Eval (Nat × List Value) := do
  match value with
  | .ref address =>
      match (← get)[address]? with
      | some (.list items) => return (address, items)
      | some (.bytearray _) => error "TypeError"
      | none => unsupported
  | _ => error "TypeError"

def index (items : List α) (value : Value) : Eval Nat := do
  let i ← match value with
    | .scalar (.int n) => pure n
    | .scalar (.bool b) => pure (if b then 1 else 0)
    | _ => error "TypeError"
  let i := if i < 0 then i + items.length else i
  if i < 0 ∨ i ≥ items.length then error "IndexError" else return i.toNat

def truth (value : Value) : Eval Bool := do
  match value with
  | .scalar c => return scalarTruth c
  | .ref address =>
      match (← get)[address]? with
      | some (.list items) => return !items.isEmpty
      | some (.bytearray bytes) => return !bytes.isEmpty
      | none => unsupported

/-- Formatting is partial; ordinary invalid operand combinations raise TypeError. -/
def invalidBinary (op : BinOp) (left : Value) : Eval Value := do
  if op == .mod then
    match left with
    | .scalar (.bytes _) => unsupported
    | .ref address =>
        match (← get)[address]? with
        | some (.bytearray _) => unsupported
        | some (.list _) => error "TypeError"
        | none => unsupported
    | _ => error "TypeError"
  else error "TypeError"

def binary (op : BinOp) (a b : Value) : Eval Value := do
  let number : Value → Value
    | .scalar (.bool b) => .scalar (.int (if b then 1 else 0))
    | v => v
  match number a, number b with
  | .ref left, .ref right =>
      if op == .add then
        match (← get)[left]?, (← get)[right]? with
        | some (.bytearray xs), some (.bytearray ys) => allocateBuffer (xs ++ ys)
        | some (.list _), some (.list _) => allocate ((← array a).2 ++ (← array b).2)
        | none, _ | _, none => unsupported
        | _, _ => error "TypeError"
      else invalidBinary op a
  | .ref address, .scalar (.int n) | .scalar (.int n), .ref address =>
      if op == .mult then
        match (← get)[address]? with
        | some (.bytearray bytes) => allocateBuffer (List.replicate n.toNat bytes).flatten
        | some (.list _) => allocate ((List.replicate n.toNat (← array (.ref address)).2).flatten)
        | none => unsupported
      else invalidBinary op a
  | .ref address, .scalar (.bytes bytes) =>
      if op == .add then
        match (← get)[address]? with
        | some (.bytearray left) => allocateBuffer (left ++ bytes)
        | some (.list _) => error "TypeError"
        | none => unsupported
      else invalidBinary op a
  | .scalar (.bytes bytes), .ref address =>
      if op == .add then
        match (← get)[address]? with
        | some (.bytearray right) => return .scalar (.bytes (bytes ++ right))
        | some (.list _) => error "TypeError"
        | none => unsupported
      else invalidBinary op a
  | .scalar (.string s), .scalar (.int n) | .scalar (.int n), .scalar (.string s) =>
      if op == .mult then return .scalar (.string (String.join (List.replicate n.toNat s)))
      else error "TypeError"
  | .scalar (.string a), .scalar (.string b) =>
      if op == .add then return .scalar (.string (a ++ b)) else error "TypeError"
  | .scalar a, .scalar b =>
      match scalarBinary op a b with
      | some (.ok v) => return .scalar v
      | some (.error e) => throw e
      | none => unsupported
  | .ref _, _ => invalidBinary op a
  | _, _ => error "TypeError"

/-- Sequence iteration for the builtin list, text and buffer types. -/
def sequence : Value → Eval (List Value)
  | .scalar (.bytes bytes) => pure (bytes.map (fun byte => .scalar (.int byte.toNat)))
  | .scalar (.string text) => pure (text.toList.map (fun char => .scalar (.string (String.singleton char))))
  | .ref address => do
      match (← get)[address]? with
      | some (.list items) => pure items
      | some (.bytearray bytes) => pure (bytes.map (fun byte => .scalar (.int byte.toNat)))
      | none => unsupported
  | _ => error "TypeError"

/-- Reading a length never copies or changes the referenced object. -/
def length : Value → Eval Value
  | .scalar (.string text) => pure (.scalar (.int text.length))
  | .scalar (.bytes bytes) => pure (.scalar (.int bytes.length))
  | .scalar _ => error "TypeError"
  | .ref address => do
      match (← get)[address]? with
      | some (.list items) => return .scalar (.int items.length)
      | some (.bytearray bytes) => return .scalar (.int bytes.length)
      | none => unsupported

def getItem (value subscript : Value) : Eval Value := do
  match value, subscript with
  | .scalar value, .scalar subscript =>
      match Strings.get value subscript with
      | .ok value => return .scalar value
      | .error exception => throw exception
  | .ref address, subscript =>
      match (← get)[address]? with
      | some (.list items) => return (items[← index items subscript]?).getD (.scalar .none)
      | some (.bytearray bytes) => return .scalar (.int ((bytes[← index bytes subscript]?).getD 0).toNat)
      | none => unsupported
  | _, _ => error "TypeError"

/-- Reading a valid buffer index preserves the shared heap. -/
theorem getItem_buffer (heap : Heap) (address position : Nat) (bytes : List UInt8)
    (found : heap[address]? = some (.bytearray bytes)) (valid : position < bytes.length) :
    getItem (.ref address) (.scalar (.int position)) heap =
      some (.ok (.scalar (.int bytes[position].toNat)), heap) := by
  have nonnegative : ¬ (position : Int) < 0 := by omega
  have inside : ¬ bytes.length ≤ position := by omega
  simp [getItem, found, index, nonnegative, inside, Except.map, List.getElem?_eq_getElem valid]

/-- Index type is checked before the byte, but its range is checked after it. -/
def setItem (value subscript replacement : Value) : Eval Value := do
  match value with
  | .ref address =>
      match (← get)[address]? with
      | some (.list items) =>
          let i ← index items subscript
          modify fun heap => heap.set address (.list (items.set i replacement))
          return .scalar .none
      | some (.bytearray bytes) =>
          let n ← integer subscript
          let byte ← byte replacement
          let i ← index bytes (.scalar (.int n))
          modify fun heap => heap.set address (.bytearray (bytes.set i byte))
          return .scalar .none
      | none => unsupported
  | _ => error "TypeError"

/-- Writing an in-range byte preserves the buffer address and every other object. -/
theorem setItem_buffer (heap : Heap) (address position : Nat) (bytes : List UInt8) (value : UInt8)
    (found : heap[address]? = some (.bytearray bytes)) (valid : position < bytes.length) :
    setItem (.ref address) (.scalar (.int position)) (.scalar (.int value.toNat)) heap =
      some (.ok (.scalar .none), heap.set address (.bytearray (bytes.set position value))) := by
  have byteRange : (value.toNat : Int) < 256 := by
    have bound := value.toNat_lt
    omega
  have nonnegative : ¬ (position : Int) < 0 := by omega
  have inside : ¬ bytes.length ≤ position := by omega
  simp [setItem, found, integer, byte, index, byteRange, nonnegative, inside, Except.map]

private def sliceBound : Value → Eval (Option Int)
  | .scalar .none => pure none
  | value => some <$> integer value

/-- Expressions are already evaluated; index conversion checks the step first. -/
def sliceBounds (lower upper stride : Value) : Eval Py.Builtin.Slice.Slice := do
  let stride ← sliceBound stride
  if stride = some 0 then error "ValueError"
  else
    let lower ← sliceBound lower
    let upper ← sliceBound upper
    return ⟨lower, upper, stride⟩

private def sequenceResult (result : Py.Builtin.Result α) : Eval α :=
  match result with
  | .ok value => pure value
  | .error (.indexError _) => error "IndexError"
  | .error (.valueError _) => error "ValueError"
  | .error (.typeError _) => error "TypeError"
  | .error _ => unsupported

def getSlice (value lower upper stride : Value) : Eval Value := do
  match value with
  | .scalar scalar =>
      match scalar with
      | .bytes _ | .string _ =>
          let bounds ← sliceBounds lower upper stride
          let encode := fun (bound : Option Int) => (bound.map Constant.int).getD .none
          match Strings.slice scalar (encode bounds.start) (encode bounds.stop) (encode bounds.step) with
          | .ok value => return .scalar value
          | .error exception => throw exception
      | _ => error "TypeError"
  | .ref address =>
      match (← get)[address]? with
      | some (.list items) =>
          let bounds ← sliceBounds lower upper stride
          allocate (← sequenceResult (Py.Builtin.Sequence.slice items bounds))
      | some (.bytearray bytes) =>
          let bounds ← sliceBounds lower upper stride
          allocateBuffer (← sequenceResult (Py.Builtin.Sequence.slice bytes bounds))
      | none => unsupported

def setSlice (value lower upper stride replacement : Value) : Eval Value := do
  match value with
  | .ref address =>
      match (← get)[address]? with
      | some (.list items) =>
          let bounds ← sliceBounds lower upper stride
          let replacement ← sequence replacement
          let result ← sequenceResult (Py.Builtin.List.setSlice items bounds replacement)
          modify fun heap => heap.set address (.list result)
          return .scalar .none
      | some (.bytearray bytes) =>
          let bounds ← sliceBounds lower upper stride
          let replacement ← byteValues replacement
          let result ← sequenceResult (Py.Builtin.ByteArray.setSlice bytes bounds replacement)
          modify fun heap => heap.set address (.bytearray result)
          return .scalar .none
      | none => unsupported
  | _ => error "TypeError"

/-- Lift a pure buffer slice update to the shared heap without changing its address. -/
theorem setSlice_buffer (heap : Heap) (address : Nat) (bytes replacement updated : List UInt8)
    (lower upper stride : Value) (bounds : Py.Builtin.Slice.Slice)
    (found : heap[address]? = some (.bytearray bytes))
    (normalized : sliceBounds lower upper stride heap = some (.ok bounds, heap))
    (update : Py.Builtin.ByteArray.setSlice bytes bounds replacement = .ok updated) :
    setSlice (.ref address) lower upper stride (.scalar (.bytes replacement)) heap =
      some (.ok (.scalar .none), heap.set address (.bytearray updated)) := by
  simp [setSlice, found, normalized, byteValues, update, sequenceResult, Except.map]

/-- Resolve append before its argument is evaluated. Both heap object kinds expose it. -/
def appendReceiver (value : Value) : Eval Nat := do
  match value with
  | .ref address =>
      match (← get)[address]? with
      | some _ => return address
      | none => unsupported
  | .scalar _ => error "AttributeError"

def appendItem (address : Nat) (value : Value) : Eval Value := do
  match (← get)[address]? with
  | some (.list items) =>
      modify fun heap => heap.set address (.list (items ++ [value]))
      return .scalar .none
  | some (.bytearray bytes) =>
      let byte ← byte value
      modify fun heap => heap.set address (.bytearray (bytes ++ [byte]))
      return .scalar .none
  | none => unsupported

def expr (env : Env) : Expr → Eval Value
  | .constant c => pure (.scalar c)
  | .name name => match env name with
      | some v => pure v
      | none => error "UnboundLocalError"
  | .list items => do allocate (← items.mapM (expr env))
  | .subscript base sub => do
      let value ← expr env base
      let i ← expr env sub
      let (_, items) ← array value
      return (items[← index items i]?).getD (.scalar .none)
  | .binOp a op b => do
      let a ← expr env a
      let b ← expr env b
      binary op a b
  | .unaryOp .not a => do return .scalar (.bool (!(← truth (← expr env a))))
  | .unaryOp .uSub a => do
      match ← expr env a with
      | .scalar (.int n) => return .scalar (.int (-n))
      | .scalar (.bool b) => return .scalar (.int (if b then -1 else 0))
      | _ => error "TypeError"
  | .compare a [(op, b)] => do
      let a ← expr env a
      let b ← expr env b
      match a, b with
      | .scalar a, .scalar b => match scalarCompare op a b with
          | some v => return .scalar (.bool v)
          | none => error "TypeError"
      | _, _ => unsupported -- recursive Python list equality needs its own execution
  | .call (.name "len") [a] | .builtinCall .len [a] => do
      length (← expr env a)
  | .call (.attribute base "append") [item] => do
      let value ← expr env base
      let item ← expr env item
      let (address, items) ← array value
      modify fun heap => heap.set address (.list ((items ++ [item])))
      return .scalar .none
  | _ => unsupported

def assign (env : Env) (target : Expr) (value : Value) : Eval Env := do
  match target with
  | .name name => return fun query => if query = name then some value else env query
  | .subscript base sub =>
      let base ← expr env base
      let sub ← expr env sub
      let (address, items) ← array base
      let i ← index items sub
      modify fun heap => heap.set address (.list ((items.set i value)))
      return env
  | _ => unsupported

structure State where
  todo : List Stmt
  env : Env
  heap : Heap

/-- The module bindings and entry objects are observed on all exit paths. -/
def completion (initial : Globals) (declared : List String) (anchors : Nat)
    (env : Env) (heap : Heap) (outcome : Except ExceptionObject Value) : Completion :=
  ⟨outcome, initial.map (fun (name, old) =>
    (name, if name ∈ declared then (env name).getD old else old)), heap, anchors⟩

def step (initial : Globals) (declared : List String) (anchors : Nat)
    (state : State) : Step State Completion :=
  let done := fun heap outcome => Step.done (.ok (completion initial declared anchors state.env heap outcome))
  let run := fun {α : Type} (action : Eval α) (next : α → Heap → Step State Completion) =>
    match action state.heap with
    | none => .unsupported
    | some (.error e, heap) => done heap (.error e)
    | some (.ok v, heap) => next v heap
  match state.todo with
  | [] => done state.heap (.ok (.scalar .none))
  | .globalDecl _ :: rest => .next { state with todo := rest }
  | .return value :: _ => run (expr state.env value) (fun v heap => done heap (.ok v))
  | .assign [target] value :: rest =>
      run (do assign state.env target (← expr state.env value)) fun env heap => .next ⟨rest, env, heap⟩
  | .augAssign (.subscript base sub) op value :: rest =>
      run (do
        -- Python evaluates the receiver and index once, reads before the RHS,
        -- then applies that same index to the possibly changed list on write.
        let base ← expr state.env base
        let sub ← expr state.env sub
        let (_, items) ← array base
        let i ← index items sub
        let left := (items[i]?).getD (.scalar .none)
        let right ← expr state.env value
        let result ← binary op left right
        let (address, updated) ← array base
        let i ← index updated sub
        modify fun heap => heap.set address (.list ((updated.set i result)))
        pure state.env) fun env heap => .next ⟨rest, env, heap⟩
  | .augAssign target op value :: rest =>
      run (do
        let left ← expr state.env target
        let right ← expr state.env value
        let result ← match left, right, op with
          | .ref address, .ref _, .add => do
              let items := (← array left).2 ++ (← array right).2
              modify fun heap => heap.set address (.list (items))
              pure left
          | .ref address, .scalar (.string text), .add => do
              let items := (← array left).2 ++ text.toList.map (fun c =>
                Value.scalar (.string (String.singleton c)))
              modify fun heap => heap.set address (.list (items))
              pure left
          | .ref address, .scalar (.int n), .mult => do
              let items := (List.replicate n.toNat (← array left).2).flatten
              modify fun heap => heap.set address (.list (items))
              pure left
          | .ref address, .scalar (.bool b), .mult => do
              let old ← array left
              let items := if b then old.2 else []
              modify fun heap => heap.set address (.list (items))
              pure left
          | _, _, _ => binary op left right
        assign state.env target result) fun env heap => .next ⟨rest, env, heap⟩
  | .expr value :: rest => run (expr state.env value) fun _ heap => .next ⟨rest, state.env, heap⟩
  | .ifThen test yes no :: rest => run (do truth (← expr state.env test)) fun b heap =>
      .next ⟨(if b then yes else no) ++ rest, state.env, heap⟩
  | .whileDo test body otherwise :: rest => run (do truth (← expr state.env test)) fun b heap =>
      .next ⟨if b then body ++ [.whileDo test body otherwise] ++ rest else otherwise ++ rest, state.env, heap⟩
  | .raise (some (.call (.name name) args)) :: _ => run (args.mapM fun a => do
        match ← expr state.env a with
        | .scalar c => pure c
        | _ => unsupported) fun args heap => done heap (.error ⟨name, args⟩)
  | .raise (some (.name name)) :: _ => done state.heap (.error ⟨name, []⟩)
  | .assert test none :: rest => run (do truth (← expr state.env test)) fun b heap =>
      if b then .next ⟨rest, state.env, heap⟩ else done heap (.error ⟨"AssertionError", []⟩)
  | _ => .unsupported

/-- All entry lists share one heap. Initializers specify input domains, not a
 fixed starting state. This interpreter executes the translated function body. -/
def function (module : Module) (name : String) (values : List Value)
    (globals : Globals) (heap : Heap) : Call :=
  ⟨match findFunctionIn module.body name with
  | none => Execution.unsupported
  | some (args, body) =>
      let declared := blockGlobals body
      let locals := (blockLocals body).filter (fun name => name ∉ declared)
      if args.length = values.length ∧ (globals.map Prod.fst).Nodup ∧
          declared.all (fun name => (globals.lookup name).isSome) then
        let env : Env := fun name =>
          if name ∈ args.map Arg.name then ((args.map Arg.name).zip values).lookup name
          else if name ∈ locals then none else globals.lookup name
        ⟨State, ⟨executableBody body, env, heap⟩, step globals declared heap.length⟩
      else Execution.unsupported⟩

end FormalSW.PyAst.Mutable
