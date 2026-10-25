import lang.py.FormalSW.Globals
import lang.py.FormalSW.GraphPreservation
import lang.py.builtin.type.bytearray
import lang.py.FormalSW.Strings
import lang.py.FormalSW.ScalarDicts
import lang.py.FormalSW.HashDicts

namespace FormalSW.PyAst.Mutable

/-- References are shared by arguments, globals, locals, and returned values. -/
inductive Value where
  | scalar (value : Constant)
  | ref (address : Nat)
deriving Repr, DecidableEq

/-- Heap objects have stable addresses and retain their runtime type. -/
inductive Object where
  | list (items : List Value)
  | tuple (items : List Value)
  | bytearray (bytes : List UInt8)
  | set (items : List Constant)
  /-- Tuple-containing sets retain their original representatives and references. -/
  | keySet (items : List (HashKey × Value))
  | dict (entries : List (Constant × Value))
  /-- Tuple keys retain their actual representative and all shared references. -/
  | keyDict (entries : List (HashDict.Entry Value))
  /-- Plain instances have ordered fields and no custom special methods. -/
  | instance (origin name : String) (fields : List (String × Value))
  /-- Dataclass fields drive generated equality; frozen instances reject writes. -/
  | dataInstance (origin name : String) (frozen : Bool) (declared : List String)
      (fields : List (String × Value))
deriving Repr, DecidableEq

abbrev Heap := List Object
abbrev Globals := List (String × Value)
abbrev Env := String → Option Value

def Value.edge : Value → Graph.Edge
  | .scalar c => .scalar c
  | .ref n => .ref n

/-- Follow the finite annotation structure through the shared heap. -/
def Value.ListHasType (heap : Heap) (value : Value) (kind : String) : Prop :=
  match value with
  | .scalar _ => False
  | .ref address => ∃ items, heap[address]? = some (.list items) ∧
      (kind = "list" ∨ ∃ elementKind, ∃ (_ : kind = "list[" ++ elementKind ++ "]"),
        ∀ item ∈ items, match item with
          | .scalar (.int _) => elementKind = "int"
          | .scalar (.string _) => elementKind = "str"
          | .scalar (.bool _) => elementKind = "bool"
          | .ref _ => elementKind.startsWith "list[" = true ∧ Value.ListHasType heap item elementKind
          | _ => False)
termination_by kind.length
decreasing_by
  subst kind
  simp only [String.length_append]
  change elementKind.length < 5 + elementKind.length + 1
  omega

/-- Annotation names differ from runtime type names only for None. -/
def scalarKind : Constant → String
  | .none => "None"
  | value => (Data.scalar value).typeName

/-- Parse the supported scalar-key, scalar-value dictionary annotations. -/
def dictionaryKinds (kind : String) : Option (String × String) :=
  let kinds := ["int", "str", "bytes", "bool", "None"]
  kinds.findSome? fun keyKind => kinds.findSome? fun valueKind =>
    if kind = "dict[" ++ keyKind ++ "," ++ valueKind ++ "]" then some (keyKind, valueKind)
    else none

/-- The input dictionary keeps its address and insertion order; aliases are permitted. -/
def Value.DictionaryHasType (heap : Heap) (value : Value) (keyKind valueKind : String) : Prop :=
  match value with
  | .scalar _ => False
  | .ref address => ∃ entries, heap[address]? = some (.dict entries) ∧
      ∀ entry ∈ entries, scalarKind entry.1 = keyKind ∧
        ∃ scalar, entry.2 = .scalar scalar ∧ scalarKind scalar = valueKind

def Value.HasType (heap : Heap) (value : Value) (kind : String) : Prop :=
  match value with
  | .scalar (.int _) => kind = "int"
  | .scalar (.string _) => kind = "str"
  | .scalar (.bytes _) => kind = "bytes"
  | .scalar (.bool _) => kind = "bool"
  | .scalar .none => kind = "None"
  | .ref address => match dictionaryKinds kind with
    | some (keyKind, valueKind) => Value.DictionaryHasType heap value keyKind valueKind
    | none => if kind = "bytearray" then
        ∃ bytes, heap[address]? = some (.bytearray bytes)
      else if kind = "set" ∨ kind = "set[int]" ∨ kind = "set[str]" ∨ kind = "set[bool]" then
        ∃ items, heap[address]? = some (.set items) ∧
          (kind = "set" ∨ ∃ elementKind, kind = "set[" ++ elementKind ++ "]" ∧
            ∀ item ∈ items, (Data.scalar item).typeName = elementKind)
      else ∃ items, heap[address]? = some (.list items) ∧
        (kind = "list" ∨ ∃ elementKind, ∃ (_ : kind = "list[" ++ elementKind ++ "]"),
          ∀ item ∈ items, match item with
            | .scalar (.int _) => elementKind = "int"
            | .scalar (.string _) => elementKind = "str"
            | .scalar (.bool _) => elementKind = "bool"
            | .ref _ => elementKind.startsWith "list[" = true ∧ Value.ListHasType heap item elementKind
            | _ => False)

theorem Value.ListHasType.of_heap_preserved {heap other : Heap} (typed : Value.ListHasType heap value kind)
    (preserved : ∀ (address : Nat) (object : Object), heap[address]? = some object → other[address]? = some object) :
    Value.ListHasType other value kind := by
  rw [Value.ListHasType.eq_def] at typed ⊢
  cases value with
  | scalar _ => exact typed.elim
  | ref address =>
      obtain ⟨items, found, kinds⟩ := typed
      refine ⟨items, preserved address _ found, ?_⟩
      rcases kinds with plain | ⟨elementKind, domain, elements⟩
      · exact .inl plain
      · refine .inr ⟨elementKind, domain, ?_⟩
        intro item member
        have inner := elements item member
        cases item with
        | scalar constant => cases constant <;> exact inner
        | ref row => exact ⟨inner.1, inner.2.of_heap_preserved preserved⟩
termination_by kind.length
decreasing_by
  subst kind
  simp only [String.length_append]
  change elementKind.length < 5 + elementKind.length + 1
  omega

/-- Allocating other objects preserves types, including shared nested lists. -/
theorem Value.HasType.of_heap_preserved {heap other : Heap} (typed : Value.HasType heap value kind)
    (preserved : ∀ (address : Nat) (object : Object), heap[address]? = some object → other[address]? = some object) :
    Value.HasType other value kind := by
  cases value with
  | scalar constant => cases constant <;> exact typed
  | ref address =>
      cases parsed : dictionaryKinds kind with
      | some kinds =>
          rcases kinds with ⟨keyKind, valueKind⟩
          simp only [Value.HasType, parsed, Value.DictionaryHasType] at typed ⊢
          obtain ⟨entries, found, types⟩ := typed
          exact ⟨entries, preserved address _ found, types⟩
      | none =>
          simp only [Value.HasType, parsed] at typed ⊢
          by_cases buffer : kind = "bytearray"
          · simp only [if_pos buffer] at typed ⊢
            obtain ⟨bytes, found⟩ := typed
            exact ⟨bytes, preserved address _ found⟩
          · simp only [if_neg buffer] at typed ⊢
            by_cases isSet : kind = "set" ∨ kind = "set[int]" ∨ kind = "set[str]" ∨ kind = "set[bool]"
            · simp only [if_pos isSet] at typed ⊢
              obtain ⟨items, found, kinds⟩ := typed
              exact ⟨items, preserved address _ found, kinds⟩
            · simp only [if_neg isSet] at typed ⊢
              obtain ⟨items, found, kinds⟩ := typed
              refine ⟨items, preserved address _ found, ?_⟩
              rcases kinds with plain | ⟨elementKind, domain, elements⟩
              · exact .inl plain
              · refine .inr ⟨elementKind, domain, ?_⟩
                intro item member
                have inner := elements item member
                cases item with
                | scalar constant => cases constant <;> exact inner
                | ref row => exact ⟨inner.1, inner.2.of_heap_preserved preserved⟩

theorem Value.dictionary_of_hasType
    (typed : Value.HasType heap (.ref address) kind)
    (parsed : dictionaryKinds kind = some (keyKind, valueKind)) :
    Value.DictionaryHasType heap (.ref address) keyKind valueKind := by
  simpa only [Value.HasType, parsed] using typed

theorem Value.HasType.append (typed : Value.HasType heap value kind) (extra : Heap) :
    Value.HasType (heap ++ extra) value kind := by
  apply typed.of_heap_preserved
  intro address object found
  have bounded : address < heap.length := by
    by_cases inside : address < heap.length
    · exact inside
    · have missing := List.getElem?_eq_none (Nat.le_of_not_gt inside)
      simp [missing] at found
  rw [List.getElem?_append_left bounded]
  exact found

/-- Nested annotations describe the same shared heap, so rows may alias. -/
theorem Value.lists_of_hasType (typed : Value.HasType heap (.ref address) "list[list[int]]") :
    ∃ rows : List Nat, heap[address]? = some (.list (rows.map Value.ref)) ∧
      ∀ row ∈ rows, Value.HasType heap (.ref row) "list[int]" := by
  obtain ⟨items, found, kinds⟩ := typed
  have elements : ∀ item ∈ items, ∃ row, item = .ref row ∧ Value.HasType heap (.ref row) "list[int]" := by
    rcases kinds with impossible | ⟨kind, domain, kinds⟩
    · simp at impossible
    · have equal : kind = "list[int]" := by
        change "list[" ++ "list[int]" ++ "]" = "list[" ++ kind ++ "]" at domain
        have chars := congrArg String.toList domain.symm
        simp only [String.toList_append] at chars
        exact String.toList_injective (List.append_cancel_left (List.append_cancel_right chars))
      subst kind
      intro item member
      have typed := kinds item member
      cases item with
      | ref row =>
          have nested := typed.2
          rw [Value.ListHasType] at nested
          exact ⟨row, rfl, nested⟩
      | scalar value => cases value <;> simp_all
  have contents : ∃ rows : List Nat, items = rows.map Value.ref ∧
      ∀ row ∈ rows, Value.HasType heap (.ref row) "list[int]" := by
    clear found kinds
    induction items with
    | nil => exact ⟨[], rfl, by simp⟩
    | cons item rest ih =>
        obtain ⟨row, rfl, typed⟩ := elements item (by simp)
        obtain ⟨rows, same, types⟩ := ih (by intro item member; exact elements item (by simp [member]))
        exact ⟨row :: rows, by simp [same], by simpa using And.intro typed types⟩
  obtain ⟨rows, rfl, types⟩ := contents
  exact ⟨rows, found, types⟩

/-- Recover mathematical integer contents without changing the object's address. -/
theorem Value.ints_of_hasType (typed : Value.HasType heap (.ref address) "list[int]") :
    ∃ xs : List Int, heap[address]? = some (.list (xs.map fun n => .scalar (.int n))) := by
  obtain ⟨items, found, kinds⟩ := typed
  have elements : ∀ item ∈ items, ∃ n, item = .scalar (.int n) := by
    rcases kinds with impossible | ⟨kind, domain, kinds⟩
    · simp at impossible
    · have equal : kind = "int" := by
        change "list[" ++ "int" ++ "]" = "list[" ++ kind ++ "]" at domain
        have chars := congrArg String.toList domain.symm
        simp only [String.toList_append] at chars
        exact String.toList_injective (List.append_cancel_left (List.append_cancel_right chars))
      subst kind
      intro item member
      have typed := kinds item member
      cases item with
      | ref address => simp_all
      | scalar value => cases value <;> simp_all
  have contents : ∃ xs : List Int, items = xs.map (fun n => Value.scalar (.int n)) := by
    clear found kinds
    induction items with
    | nil => exact ⟨[], rfl⟩
    | cons item items ih =>
        obtain ⟨n, rfl⟩ := elements item (by simp)
        obtain ⟨xs, same⟩ := ih (by intro value member; exact elements value (by simp [member]))
        exact ⟨n :: xs, by simp [same]⟩
  obtain ⟨xs, rfl⟩ := contents
  exact ⟨xs, found⟩

/-- Recover mathematical string contents without changing the object's address. -/
theorem Value.strings_of_hasType (typed : Value.HasType heap (.ref address) "list[str]") :
    ∃ xs : List String, heap[address]? = some (.list (xs.map fun n => .scalar (.string n))) := by
  obtain ⟨items, found, kinds⟩ := typed
  have elements : ∀ item ∈ items, ∃ n, item = .scalar (.string n) := by
    rcases kinds with impossible | ⟨kind, domain, kinds⟩
    · simp at impossible
    · have equal : kind = "str" := by
        change "list[" ++ "str" ++ "]" = "list[" ++ kind ++ "]" at domain
        have chars := congrArg String.toList domain.symm
        simp only [String.toList_append] at chars
        exact String.toList_injective (List.append_cancel_left (List.append_cancel_right chars))
      subst kind
      intro item member
      have typed := kinds item member
      cases item with
      | ref address => simp_all
      | scalar value => cases value <;> simp_all
  have contents : ∃ xs : List String, items = xs.map (fun n => Value.scalar (.string n)) := by
    clear found kinds
    induction items with
    | nil => exact ⟨[], rfl⟩
    | cons item items ih =>
        obtain ⟨n, rfl⟩ := elements item (by simp)
        obtain ⟨xs, same⟩ := ih (by intro value member; exact elements value (by simp [member]))
        exact ⟨n :: xs, by simp [same]⟩
  obtain ⟨xs, rfl⟩ := contents
  exact ⟨xs, found⟩

/-- Resolve keys without invoking user-defined hashing or equality. -/
private def collectKeys (resolve : Value → Option (Except ExceptionObject HashKey)) :
    List Value → Option (Except ExceptionObject (List HashKey))
  | [] => some (.ok [])
  | value :: rest => do
      match ← resolve value with
      | .error exception => return .error exception
      | .ok key => return (← collectKeys resolve rest).map (key :: ·)

/-- A tuple path contains at most heap.length distinct addresses. Exhaustion
rejects malformed cyclic tuple heaps; ordinary immutable tuples form a DAG. -/
def keyOfFuel (heap : Heap) : Nat → Value → Option (Except ExceptionObject HashKey)
  | _, .scalar value => some (.ok (.scalar value))
  | 0, .ref _ => none
  | fuel + 1, .ref address => match heap[address]? with
      | some (.tuple items) => (collectKeys (keyOfFuel heap fuel) items).map (Except.map HashKey.tuple)
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) | none => none
      | some _ => some (.error { typeName := "TypeError", args := [] })

def keyOf (heap : Heap) (value : Value) : Option (Except ExceptionObject HashKey) :=
  keyOfFuel heap (heap.length + 1) value

def keyContains (items : List (HashKey × Value)) (key : HashKey) : Bool :=
  items.any fun item => HashKey.equal item.1 key

/-- Preserve the original representative and tuple reference on duplicate insertion. -/
def insertKey (items : List (HashKey × Value)) (entry : HashKey × Value) : List (HashKey × Value) :=
  if keyContains items entry.1 then items else items ++ [entry]

def keyEntries : Object → Option (List (HashKey × Value))
  | .set items => some (items.map fun item => (.scalar item, .scalar item))
  | .keySet items => some items
  | _ => none

def compareKeySets (op : CmpOp) (left right : List (HashKey × Value)) : Bool :=
  let subset := fun xs ys => xs.all fun item => keyContains ys item.1
  match op with
  | .eq => subset left right && subset right left
  | .notEq => !(subset left right && subset right left)
  | .lt => subset left right && !subset right left
  | .ltE => subset left right
  | .gt => subset right left && !subset left right
  | .gtE => subset right left

def canonicalKeys (items : List (HashKey × Value)) : List (HashKey × Value) :=
  items.mergeSort fun left right => HashKey.before left.1 right.1

/-- Cached keys match their immutable representatives; all stored references
remain ordinary heap edges, including aliases to entry objects. -/
def KeySetValid (heap : Heap) (items : List (HashKey × Value)) : Prop :=
  items.Pairwise (fun left right => HashKey.equal left.1 right.1 = false) ∧
    ∀ entry ∈ items, keyOf heap entry.2 = some (.ok entry.1) ∧
      match entry.2 with
      | .scalar _ => True
      | .ref address => address < heap.length

/-- Cached dictionary keys preserve both key and value edges. -/
def KeyDictValid (heap : Heap) (entries : List (HashDict.Entry Value)) : Prop :=
  entries.Pairwise (fun left right => HashKey.equal left.1 right.1 = false) ∧
    ∀ entry ∈ entries, keyOf heap entry.2.1 = some (.ok entry.1) ∧
      entry.2.1.edge.Within heap.length ∧ entry.2.2.edge.Within heap.length

/-- Every reference points into the heap; cycles and sharing are permitted. -/
def Heap.Valid (heap : Heap) : Prop :=
  ∀ object ∈ heap, match object with
    | .bytearray _ => True
    | .set items => ScalarSet.Valid items
    | .keySet items => KeySetValid heap items
    | .keyDict entries => KeyDictValid heap entries
    | .dict entries => ScalarDict.Valid entries ∧
        ∀ entry ∈ entries, match entry.2 with
          | .scalar _ => True
          | .ref address => address < heap.length
    | .instance _ _ fields | .dataInstance _ _ _ _ fields => (fields.map Prod.fst).Nodup ∧
        ∀ field ∈ fields, match field.2 with
          | .scalar _ => True
          | .ref address => address < heap.length
    | .list items | .tuple items => ∀ value ∈ items, match value with
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
      | .instance origin name fields | .dataInstance origin name _ _ fields =>
          ⟨.staticObject origin name, fields.map Prod.fst, fields.map (fun field => field.2.edge)⟩
      | .list items => ⟨.list, [], items.map Value.edge⟩
      | .tuple items => ⟨.tuple, [], items.map Value.edge⟩
      | .dict entries => ⟨.dict, [], entries.flatMap (fun (key, value) => [.scalar key, value.edge])⟩
      | .keyDict entries => ⟨.dict, [], entries.flatMap (fun entry => [entry.2.1.edge, entry.2.2.edge])⟩
      | .set items => ⟨.set, [], (ScalarSet.canonical items).map Graph.Edge.scalar⟩
      | .keySet items => ⟨.set, [], (canonicalKeys items).map (fun entry => entry.2.edge)⟩
      | .bytearray bytes => ⟨.bytearray, [], bytes.map (fun byte => .scalar (.int byte.toNat))⟩)).encode

/-- Exact identical states are a fast path. Otherwise compare the rooted object
 graph using the interpreted Python comparison, preserving aliases and cycles. -/
def Completion.Equivalent (a b : Completion) : Prop :=
  a = b ∨ (a.anchors = b.anchors ∧ a.globals.map Prod.fst = b.globals.map Prod.fst ∧
    (match a.outcome, b.outcome with
      | .ok _, .ok _ => True
      | .error x, .error y => x = y
      | _, _ => False) ∧ Graph.Equivalent a.snapshot b.snapshot)

/-- Allocation alone is unobservable when all returned and global references still
point into the unchanged entry heap. Aliases and cycles in that heap are retained. -/
theorem Completion.equivalent_allocations (heap leftExtra rightExtra : Heap) (result : Value) (globals : Globals)
    (valid : heap.Valid)
    (resultWithin : result.edge.Within heap.length)
    (globalsWithin : ∀ entry ∈ globals, entry.2.edge.Within heap.length) :
    Completion.Equivalent ⟨.ok result, globals, heap ++ leftExtra, heap.length⟩
      ⟨.ok result, globals, heap ++ rightExtra, heap.length⟩ := by
  refine Or.inr ⟨rfl, rfl, trivial, ?_⟩
  let encode : Object → Graph.Node := fun object => match object with
    | .instance origin name fields | .dataInstance origin name _ _ fields =>
        ⟨.staticObject origin name, fields.map Prod.fst, fields.map (fun field => field.2.edge)⟩
    | .list items => ⟨.list, [], items.map Value.edge⟩
    | .tuple items => ⟨.tuple, [], items.map Value.edge⟩
    | .dict entries => ⟨.dict, [], entries.flatMap (fun (key, value) => [.scalar key, value.edge])⟩
    | .keyDict entries => ⟨.dict, [], entries.flatMap (fun entry => [entry.2.1.edge, entry.2.2.edge])⟩
    | .set items => ⟨.set, [], (ScalarSet.canonical items).map Graph.Edge.scalar⟩
    | .keySet items => ⟨.set, [], (canonicalKeys items).map (fun entry => entry.2.edge)⟩
    | .bytearray bytes => ⟨.bytearray, [], bytes.map (fun byte => .scalar (.int byte.toNat))⟩
  have closed : ∀ node ∈ heap.map encode, ∀ edge ∈ node.edges, edge.Within heap.length := by
    intro node member edge edgeMember
    obtain ⟨object, objectMember, rfl⟩ := List.mem_map.mp member
    have objectValid := valid object objectMember
    cases object with
    | list items | tuple items =>
        obtain ⟨value, valueMember, rfl⟩ := List.mem_map.mp edgeMember
        have valueValid := objectValid value valueMember
        cases value with
        | scalar _ => trivial
        | ref _ => exact valueValid
    | «instance» origin name fields | dataInstance origin name frozen declared fields =>
        obtain ⟨field, fieldMember, rfl⟩ := List.mem_map.mp edgeMember
        have fieldValid := objectValid.2 field fieldMember
        cases value : field.2 with
        | scalar _ => trivial
        | ref _ => simpa only [value] using fieldValid
    | dict entries =>
        obtain ⟨entry, member, edgeMember⟩ := List.mem_flatMap.mp edgeMember
        rcases List.mem_cons.mp edgeMember with rfl | edgeMember
        · trivial
        · have equal := List.mem_singleton.mp edgeMember
          subst edge
          have fieldValid := objectValid.2 entry member
          cases value : entry.2 with
          | scalar _ => trivial
          | ref _ => simpa only [value] using fieldValid
    | keyDict entries =>
        obtain ⟨entry, member, edgeMember⟩ := List.mem_flatMap.mp edgeMember
        rcases List.mem_cons.mp edgeMember with rfl | edgeMember
        · exact (objectValid.2 entry member).2.1
        · exact List.mem_singleton.mp edgeMember ▸ (objectValid.2 entry member).2.2
    | bytearray bytes =>
        obtain ⟨byte, _, rfl⟩ := List.mem_map.mp edgeMember
        trivial
    | set items =>
        obtain ⟨item, _, rfl⟩ := List.mem_map.mp edgeMember
        trivial
    | keySet items =>
        obtain ⟨entry, member, rfl⟩ := List.mem_map.mp edgeMember
        have original : entry ∈ items := by simpa [canonicalKeys] using member
        have within := (objectValid.2 entry original).2
        cases value : entry.2 with
        | scalar _ => trivial
        | ref _ => simpa only [value] using within
  have rootsClosed : ∀ edge ∈ globals.map (fun entry => entry.2.edge) ++ [result.edge], edge.Within heap.length := by
    intro edge member
    rcases List.mem_append.mp member with global | returned
    · obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp global
      exact globalsWithin entry entryMember
    · simpa only [List.mem_singleton.mp returned] using resultWithin
  have equivalent := Graph.equivalent_allocations (heap.map encode) (leftExtra.map encode) (rightExtra.map encode)
    (globals.map (fun entry => entry.2.edge) ++ [result.edge])
    (by simpa only [List.length_map] using closed) (by simpa only [List.length_map] using rootsClosed)
  simpa only [Completion.snapshot, List.map_append, List.length_map, List.append_assoc, encode] using equivalent

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

/-- Sets have their own identity; elements are hashable builtin scalars. -/
def allocateSet (items : List Constant) : Eval Value := do
  let heap ← get
  set (heap ++ [.set items])
  return .ref heap.length

/-- A tuple retains references to its elements without permitting item mutation. -/
def allocateTuple (items : List Value) : Eval Value := do
  let heap ← get
  if items.isEmpty then
    match heap.findIdx? (fun object => decide (object = .tuple [])) with
    | some address => return .ref address
    | none =>
        set (heap ++ [.tuple []])
        return .ref heap.length
  else
    set (heap ++ [.tuple items])
    return .ref heap.length

/-- Python floor division and remainder, returned in a newly allocated tuple.
Unknown numeric protocols remain unsupported, on either side of the operation. -/
def divmod : List Value → Eval Value
  | [.scalar left, .scalar right] =>
      match scalarNumber left, scalarNumber right with
      | some n, some d =>
          match Py.Builtin.Int.divMod n d with
          | .ok (quotient, remainder) => allocateTuple [.scalar (.int quotient), .scalar (.int remainder)]
          | .error (.zeroDivisionError _) => error "ZeroDivisionError"
          | .error _ => unsupported
      | _, _ => error "TypeError"
  | [left, right] => do
      let heap ← get
      if [left, right].any (fun value => match value with
          | .scalar _ => false
          | .ref address => match heap[address]? with
              | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) | none => true
              | _ => false) then unsupported
      else error "TypeError"
  | _ => error "TypeError"

theorem divmod_ints (n d : Int) (nonzero : d ≠ 0) (heap : Heap) :
    divmod [.scalar (.int n), .scalar (.int d)] heap =
      some (.ok (.ref heap.length), heap ++
        [.tuple [.scalar (.int (n.fdiv d)), .scalar (.int (n - d * n.fdiv d))]]) := by
  simp [divmod, Py.Builtin.Int.divMod, Py.Builtin.Int.floorDiv, nonzero]
  rfl

def addReceiver (value : Value) : Eval Nat := do
  match value with
  | .ref address =>
      match (← get)[address]? with
      | some (.set _) | some (.keySet _) => return address
      | some _ => error "AttributeError"
      | none => unsupported
  | .scalar _ => error "AttributeError"

/-- Extract the immutable builtin key while retaining the original heap. -/
def hashKey (value : Value) : Eval HashKey := fun heap =>
  (keyOf heap value).map fun outcome => (outcome, heap)

@[simp] theorem hashKey_scalar (heap : Heap) (item : Constant) :
    hashKey (.scalar item) heap = some (.ok (.scalar item), heap) := rfl

private theorem collectKeys_scalars (heap : Heap) (fuel : Nat) (items : List Constant) :
    collectKeys (keyOfFuel heap fuel) (items.map Value.scalar) =
      some (.ok (items.map HashKey.scalar)) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp [collectKeys, keyOfFuel, ih, Except.map]

/-- Reading a tuple key preserves its address and all aliases. -/
theorem hashKey_tuple_scalars (heap : Heap) (address : Nat) (items : List Constant)
    (found : heap[address]? = some (.tuple (items.map Value.scalar))) :
    hashKey (.ref address) heap = some (.ok (.tuple (items.map HashKey.scalar)), heap) := by
  simp [hashKey, keyOf, keyOfFuel, found, collectKeys_scalars, Except.map]

/-- Duplicate insertion preserves the existing representative, including its type. -/
def addItem (address : Nat) (value : Value) : Eval Value := do
  match (← get)[address]? with
  | some (.set items) =>
      match value with
      | .scalar item =>
          modify fun heap => heap.set address (.set (ScalarSet.insert items item))
          return .scalar .none
      | .ref other => do
          let key ← hashKey (.ref other)
          let entries := items.map fun item => (HashKey.scalar item, Value.scalar item)
          modify fun heap => heap.set address (.keySet (insertKey entries (key, .ref other)))
          return .scalar .none
  | some (.keySet items) =>
      let key ← hashKey value
      modify fun heap => heap.set address (.keySet (insertKey items (key, value)))
      return .scalar .none
  | some _ => error "AttributeError"
  | none => unsupported

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
      | some (.list items) | some (.tuple items) => items.mapM byte
      | some (.set _) | some (.keySet _) | some (.dict _) | some (.keyDict _) => unsupported
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => error "TypeError"
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
      | some (.tuple _) => error "TypeError"
      | some (.set _) | some (.keySet _) | some (.dict _) | some (.keyDict _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => error "TypeError"
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
      | some (.list items) | some (.tuple items) => return !items.isEmpty
      | some (.bytearray bytes) => return !bytes.isEmpty
      | some (.set items) => return !items.isEmpty
      | some (.keySet items) => return !items.isEmpty
      | some (.dict entries) => return !entries.isEmpty
      | some (.keyDict entries) => return !entries.isEmpty
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => return true
      | none => unsupported

/-- Formatting is partial; ordinary invalid operand combinations raise TypeError. -/
def invalidBinary (op : BinOp) (left : Value) : Eval Value := do
  if op == .sub then
    match left with
    | .ref address => match (← get)[address]? with
        | some (.set _) | some (.keySet _) | none => unsupported
        | some _ => error "TypeError"
    | _ => error "TypeError"
  else if op == .mod then
    match left with
    | .scalar (.bytes _) => unsupported
    | .ref address =>
        match (← get)[address]? with
        | some (.bytearray _) => unsupported
        | some (.list _) | some (.tuple _) => error "TypeError"
        | some (.set _) | some (.keySet _) | some (.dict _) | some (.keyDict _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => error "TypeError"
        | none => unsupported
    | _ => error "TypeError"
  else error "TypeError"

def binary (op : BinOp) (a b : Value) : Eval Value :=
  match op with
  | .bitAnd => match a, b with
      | .scalar left, .scalar right =>
          match scalarBitAnd left right with
          | .ok value => pure (.scalar value)
          | .error exception => throw exception
      | _, _ => unsupported
  | .bitOr => match a, b with
      | .scalar left, .scalar right =>
          match scalarBitOr left right with
          | .ok value => pure (.scalar value)
          | .error exception => throw exception
      -- Set/dict union and user-defined operators require their own semantics.
      | _, _ => unsupported
  | .bitXor => match a, b with
      | .scalar left, .scalar right =>
          match scalarBitXor left right with
          | .ok value => pure (.scalar value)
          | .error exception => throw exception
      | _, _ => unsupported
  | .leftShift => match a, b with
      | .scalar left, .scalar right =>
          match scalarShiftLeft left right with
          | .ok value => pure (.scalar value)
          | .error exception => throw exception
      | _, _ => unsupported
  | _ => do
    let number : Value → Value
      | .scalar (.bool b) => .scalar (.int (if b then 1 else 0))
      | v => v
    match number a, number b with
    | .ref left, .ref right =>
        if op == .add then
          match (← get)[left]?, (← get)[right]? with
          | some (.bytearray xs), some (.bytearray ys) => allocateBuffer (xs ++ ys)
          | some (.list _), some (.list _) => allocate ((← array a).2 ++ (← array b).2)
          | some (.tuple xs), some (.tuple ys) =>
              if xs.isEmpty then return b
              else if ys.isEmpty then return a
              else allocateTuple (xs ++ ys)
          | none, _ | _, none => unsupported
          | _, _ => error "TypeError"
        else invalidBinary op a
    | .ref address, .scalar (.int n) | .scalar (.int n), .ref address =>
        if op == .mult then
          match (← get)[address]? with
          | some (.bytearray bytes) => allocateBuffer (List.replicate n.toNat bytes).flatten
          | some (.list _) => allocate ((List.replicate n.toNat (← array (.ref address)).2).flatten)
          | some (.tuple items) =>
              if n = 1 ∨ items.isEmpty then return .ref address
              else allocateTuple (List.replicate n.toNat items).flatten
          | some (.set _) | some (.keySet _) | some (.dict _) | some (.keyDict _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => error "TypeError"
          | none => unsupported
        else invalidBinary op a
    | .ref address, .scalar (.bytes bytes) =>
        if op == .add then
          match (← get)[address]? with
          | some (.bytearray left) => allocateBuffer (left ++ bytes)
          | some (.list _) | some (.tuple _) => error "TypeError"
          | some (.set _) | some (.keySet _) | some (.dict _) | some (.keyDict _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => error "TypeError"
          | none => unsupported
        else invalidBinary op a
    | .scalar (.bytes bytes), .ref address =>
        if op == .add then
          match (← get)[address]? with
          | some (.bytearray right) => return .scalar (.bytes (bytes ++ right))
          | some (.list _) | some (.tuple _) => error "TypeError"
          | some (.set _) | some (.keySet _) | some (.dict _) | some (.keyDict _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => error "TypeError"
          | none => unsupported
        else invalidBinary op a
    | .scalar (.string s), .scalar (.int n) | .scalar (.int n), .scalar (.string s) =>
        if op == .mult then return .scalar (.string (String.join (List.replicate n.toNat s)))
        else error "TypeError"
    | .scalar (.string a), .scalar (.string b) =>
        if op == .add then return .scalar (.string (a ++ b)) else error "TypeError"
    | .scalar (.string _), .ref _ =>
        if op == .mod then unsupported else error "TypeError"
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
      | some (.list items) | some (.tuple items) => pure items
      | some (.bytearray bytes) => pure (bytes.map (fun byte => .scalar (.int byte.toNat)))
      | some (.set _) | some (.keySet _) | some (.dict _) | some (.keyDict _) => unsupported
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => error "TypeError"
      | none => unsupported
  | _ => error "TypeError"

/-- Scalar-only key extraction for the set-construction fast path.
Tuple keys use `hashKey`; known mutable keys are unhashable. -/
def setKey : Value → Eval Constant
  | .scalar item => pure item
  | .ref address => do
      match (← get)[address]? with
      | some (.tuple _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) | none => unsupported
      | some _ => error "TypeError"

private def allScalars : List Value → Bool
  | [] => true
  | .scalar _ :: rest => allScalars rest
  | .ref _ :: _ => false

/-- Set construction preserves the scalar fast path. Tuple-containing input is
inserted in order into a fresh set, retaining the partial heap on errors. -/
def allocateSetValues (items : List Value) : Eval Value := do
  if allScalars items then
    let keys ← items.mapM setKey
    allocateSet (keys.foldl ScalarSet.insert [])
  else
    let address := (← get).length
    let _ ← allocateSet []
    let _ ← items.mapM (addItem address)
    return .ref address

/-- Construct a fresh set from builtin sequences, sets, or dictionary keys.
Custom iteration stays unsupported, including on an otherwise empty object. -/
def setFrom (source : Value) : Eval Value := do
  let items ← match source with
    | .ref address => match (← get)[address]? with
        | some (.set items) => pure (items.map Value.scalar)
        | some (.keySet items) => pure (items.map Prod.snd)
        | some (.dict entries) => pure (entries.map fun entry => Value.scalar entry.1)
        | some (.keyDict entries) => pure (entries.map fun entry => entry.2.1)
        | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) | none => unsupported
        | _ => sequence source
    | _ => sequence source
  allocateSetValues items

/-- Scalar-list construction deduplicates without changing any input object. -/
theorem setFrom_list (heap : Heap) (address : Nat) (items : List Constant)
    (found : heap[address]? = some (.list (items.map Value.scalar))) :
    setFrom (.ref address) heap = some (.ok (.ref heap.length),
      heap ++ [.set (items.foldl ScalarSet.insert [])]) := by
  have keys : (items.map Value.scalar).mapM setKey = (pure items : Eval (List Constant)) := by
    clear found
    induction items with
    | nil => rfl
    | cons item rest ih => simp only [List.map_cons, List.mapM_cons, setKey, ih]; rfl
  have scalars : allScalars (items.map Value.scalar) = true := by
    clear found keys
    induction items with
    | nil => rfl
    | cons item rest ih => simpa [allScalars] using ih
  simp [setFrom, sequence, found, allocateSetValues, scalars, keys, allocateSet, Except.map]

/-- Reverse iteration handles builtin sequences; dictionaries and custom
`__reversed__`/`__getitem__` protocols need separate execution semantics. -/
def reversibleSequence (value : Value) : Eval (List Value) := do
  match value with
  | .ref address =>
      match (← get)[address]? with
      | some (.list _) | some (.tuple _) | some (.bytearray _) => sequence value
      | some (.set _) | some (.keySet _) => error "TypeError"
      | _ => unsupported
  | .scalar _ => sequence value

/-- Reading a length never copies or changes the referenced object. -/
def length : Value → Eval Value
  | .scalar (.string text) => pure (.scalar (.int text.length))
  | .scalar (.bytes bytes) => pure (.scalar (.int bytes.length))
  | .scalar _ => error "TypeError"
  | .ref address => do
      match (← get)[address]? with
      | some (.list items) | some (.tuple items) => return .scalar (.int items.length)
      | some (.bytearray bytes) => return .scalar (.int bytes.length)
      | some (.set items) => return .scalar (.int items.length)
      | some (.keySet items) => return .scalar (.int items.length)
      | some (.dict entries) => return .scalar (.int entries.length)
      | some (.keyDict entries) => return .scalar (.int entries.length)
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => error "TypeError"
      | none => unsupported

/-- Non-scalar hash protocols are partial; mutable builtin keys are unhashable. -/
def dictionaryKey : Value → Eval Constant
  | .scalar key => pure key
  | .ref address => do
      match (← get)[address]? with
      | some (.tuple _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) | none => unsupported
      | some _ => error "TypeError"

def allocateDict (entries : List (Constant × Value)) : Eval Value := do
  let address := (← get).length
  modify fun heap => heap ++ [.dict entries]
  return .ref address

/-- Scalar-only dictionaries keep their original heap representation until a tuple is inserted. -/
def promoteDictionary (entries : List (Constant × Value)) : List (HashDict.Entry Value) :=
  entries.map fun (key, value) => (.scalar key, .scalar key, value)

/-- Return the original keys, rather than copies of their tuple representatives. -/
def dictionaryEntries : Object → Option (List (HashDict.Entry Value))
  | .dict entries => some (promoteDictionary entries)
  | .keyDict entries => some entries
  | _ => none

/-- A bound get reads the dictionary after all argument effects. -/
def dictionaryGet (address : Nat) (key defaultValue : Value) : Eval Value := do
  match (← get)[address]? with
  | some (.dict entries) =>
      match key with
      | .scalar scalar => return (ScalarDict.lookup entries scalar).getD defaultValue
      | .ref _ => return (HashDict.lookup (promoteDictionary entries) (← hashKey key)).getD defaultValue
  | some (.keyDict entries) => return (HashDict.lookup entries (← hashKey key)).getD defaultValue
  | none => unsupported
  | some _ => error "TypeError"

/-- Defaults are evaluated by the caller even when an existing value is returned. -/
def dictionarySetDefault (address : Nat) (key defaultValue : Value) : Eval Value := do
  match (← get)[address]? with
  | some (.dict entries) =>
      match key with
      | .scalar scalar =>
          match ScalarDict.lookup entries scalar with
          | some value => return value
          | none =>
              modify fun heap => heap.set address (.dict (ScalarDict.insert entries scalar defaultValue))
              return defaultValue
      | .ref _ =>
          let hashed ← hashKey key
          let promoted := promoteDictionary entries
          match HashDict.lookup promoted hashed with
          | some value => return value
          | none =>
              modify fun heap => heap.set address (.keyDict (HashDict.insert promoted hashed key defaultValue))
              return defaultValue
  | some (.keyDict entries) =>
      let hashed ← hashKey key
      match HashDict.lookup entries hashed with
      | some value => return value
      | none =>
          modify fun heap => heap.set address (.keyDict (HashDict.insert entries hashed key defaultValue))
          return defaultValue
  | none => unsupported
  | some _ => error "TypeError"

/-- Tuple-valued KeyError arguments require a heap exception object and remain partial. -/
private def missingDictionaryKey : Value → Eval Value
  | .scalar key => throw { typeName := "KeyError", args := [key] }
  | .ref _ => unsupported

def getItem (value subscript : Value) : Eval Value := do
  match value, subscript with
  | .scalar value, .scalar subscript =>
      match Strings.get value subscript with
      | .ok value => return .scalar value
      | .error exception => throw exception
  | .ref address, subscript =>
      match (← get)[address]? with
      | some (.list items) | some (.tuple items) => return (items[← index items subscript]?).getD (.scalar .none)
      | some (.bytearray bytes) => return .scalar (.int ((bytes[← index bytes subscript]?).getD 0).toNat)
      | some (.dict entries) =>
          match subscript with
          | .scalar key =>
              match ScalarDict.lookup entries key with
              | some value => return value
              | none => throw { typeName := "KeyError", args := [key] }
          | .ref _ =>
              let key ← hashKey subscript
              match HashDict.lookup (promoteDictionary entries) key with
              | some value => return value
              | none => missingDictionaryKey subscript
      | some (.keyDict entries) =>
          let key ← hashKey subscript
          match HashDict.lookup entries key with
          | some value => return value
          | none => missingDictionaryKey subscript
      | some (.set _) | some (.keySet _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => error "TypeError"
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
      | some (.dict entries) =>
          match subscript with
          | .scalar key =>
              modify fun heap => heap.set address (.dict (ScalarDict.insert entries key replacement))
              return .scalar .none
          | .ref _ =>
              let key ← hashKey subscript
              modify fun heap => heap.set address
                (.keyDict (HashDict.insert (promoteDictionary entries) key subscript replacement))
              return .scalar .none
      | some (.keyDict entries) =>
          let key ← hashKey subscript
          modify fun heap => heap.set address (.keyDict (HashDict.insert entries key subscript replacement))
          return .scalar .none
      | some (.set _) | some (.keySet _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => error "TypeError"
      | some (.tuple _) => error "TypeError"
      | none => unsupported
  | _ => error "TypeError"

/-- Reading an in-range list element preserves the shared heap. -/
theorem getItem_list (heap : Heap) (address position : Nat) (items : List Value)
    (found : heap[address]? = some (.list items)) (valid : position < items.length) :
    getItem (.ref address) (.scalar (.int position)) heap = some (.ok items[position], heap) := by
  have nonnegative : ¬ (position : Int) < 0 := by omega
  have inside : ¬ items.length ≤ position := by omega
  simp [getItem, found, index, nonnegative, inside, Except.map, List.getElem?_eq_getElem valid]

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
      | some (.tuple _) => unsupported
      | some (.bytearray bytes) =>
          let bounds ← sliceBounds lower upper stride
          allocateBuffer (← sequenceResult (Py.Builtin.Sequence.slice bytes bounds))
      | some (.dict _) | some (.keyDict _) => unsupported
      | some (.set _) | some (.keySet _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => error "TypeError"
      | none => unsupported

/-- A list prefix is a fresh object; all existing references keep their contents. -/
theorem getSlice_list_prefix (heap : Heap) (address : Nat) (items : List Value) (stop : Int)
    (found : heap[address]? = some (.list items)) :
    getSlice (.ref address) (.scalar .none) (.scalar (.int stop)) (.scalar .none) heap =
      some (.ok (.ref heap.length), heap ++ [.list (items.take (Py.Builtin.Slice.prefixLength items.length stop))]) := by
  simp [getSlice, found, sliceBounds, sliceBound, integer, Py.Builtin.Sequence.slice_prefix,
    sequenceResult, allocate, Except.map]

/-- A list suffix is a fresh object, including when its start lies past the end. -/
theorem getSlice_list_suffix (heap : Heap) (address : Nat) (items : List Value) (start : Nat)
    (found : heap[address]? = some (.list items)) :
    getSlice (.ref address) (.scalar (.int start)) (.scalar .none) (.scalar .none) heap =
      some (.ok (.ref heap.length), heap ++ [.list (items.drop start)]) := by
  simp [getSlice, found, sliceBounds, sliceBound, integer, Py.Builtin.Sequence.slice_suffix,
    sequenceResult, allocate, Except.map]

/-- A whole-list slice allocates a new list and retains each element's identity. -/
theorem getSlice_list_copy (heap : Heap) (address : Nat) (items : List Value)
    (found : heap[address]? = some (.list items)) :
    getSlice (.ref address) (.scalar .none) (.scalar .none) (.scalar .none) heap =
      some (.ok (.ref heap.length), heap ++ [.list items]) := by
  simp [getSlice, found, sliceBounds, sliceBound, Py.Builtin.Sequence.slice_full,
    sequenceResult, allocate, Except.map]

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
      | some (.dict _) | some (.keyDict _) => unsupported
      | some (.set _) | some (.keySet _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => error "TypeError"
      | some (.tuple _) => error "TypeError"
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

/-- Resolve append before its argument is evaluated. -/
def appendReceiver (value : Value) : Eval Nat := do
  match value with
  | .ref address =>
      match (← get)[address]? with
      | some (.list _) | some (.bytearray _) => return address
      | some (.set _) | some (.keySet _) | some (.dict _) | some (.keyDict _) | some (.tuple _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => error "AttributeError"
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
  | some (.set _) | some (.keySet _) | some (.dict _) | some (.keyDict _) | some (.tuple _) | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => error "AttributeError"
  | none => unsupported

/-- Remove an element from the live sequence, retaining all remaining references.
Indices use the unbounded integer semantics of the builtin sequence model. -/
def popItem (address : Nat) (subscript : Value) : Eval Value := do
  let position ← match subscript with
    | .ref indexAddress => match (← get)[indexAddress]? with
        | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => unsupported
        | some _ => error "TypeError"
        | none => unsupported
    | _ => integer subscript
  match (← get)[address]? with
  | some (.list items) =>
      let (value, remaining) ← sequenceResult (Py.Builtin.List.pop items position)
      modify fun heap => heap.set address (.list remaining)
      return value
  | some (.bytearray bytes) =>
      let (value, remaining) ← sequenceResult (Py.Builtin.List.pop bytes position)
      modify fun heap => heap.set address (.bytearray remaining)
      return .scalar (.int value.toNat)
  | some _ => error "AttributeError"
  | none => unsupported

theorem popItem_list (heap : Heap) (address position : Nat) (items : List Value)
    (found : heap[address]? = some (.list items)) (valid : position < items.length) :
    popItem address (.scalar (.int position)) heap =
      some (.ok items[position], heap.set address (.list (items.eraseIdx position))) := by
  simp [popItem, integer, found, Py.Builtin.List.pop_getElem items position valid,
    sequenceResult, Except.map]

theorem popItem_buffer (heap : Heap) (address position : Nat) (bytes : List UInt8)
    (found : heap[address]? = some (.bytearray bytes)) (valid : position < bytes.length) :
    popItem address (.scalar (.int position)) heap =
      some (.ok (.scalar (.int bytes[position].toNat)), heap.set address (.bytearray (bytes.eraseIdx position))) := by
  simp [popItem, integer, found, Py.Builtin.List.pop_getElem bytes position valid,
    sequenceResult, Except.map]

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
