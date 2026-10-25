import lang.py.FormalSW.Choices

/-! Structural annotation domains for nested lists and immutable tuples.

Every container retains its original heap address. The domain does not require
distinct addresses, copy elements, or turn a tuple into a mathematical list at
runtime. Fixed tuples check each position and its arity; variadic tuples check
every element against one domain. Existing flat annotation domains are unchanged. -/
namespace FormalSW.PyAst.Mutable

inductive ContainerType where
  | scalar (kind : String)
  | list (element : ContainerType)
  | tuple (fields : List ContainerType)
  | tupleOf (element : ContainerType)
  | dictionary (key value : ContainerType)
deriving Repr

inductive Value.HasContainerType (heap : Heap) : Value → ContainerType → Prop where
  | scalar {value : Constant} {kind : String} :
      scalarKind value = kind → HasContainerType heap (.scalar value) (.scalar kind)
  | list {address : Nat} {items : List Value} {element : ContainerType} :
      heap[address]? = some (.list items) →
      (∀ item ∈ items, HasContainerType heap item element) →
      HasContainerType heap (.ref address) (.list element)
  | fixedTuple {address : Nat} {items : List Value} {fields : List ContainerType} :
      heap[address]? = some (.tuple items) → items.length = fields.length →
      (∀ pair ∈ items.zip fields, HasContainerType heap pair.1 pair.2) →
      HasContainerType heap (.ref address) (.tuple fields)
  | variadicTuple {address : Nat} {items : List Value} {element : ContainerType} :
      heap[address]? = some (.tuple items) →
      (∀ item ∈ items, HasContainerType heap item element) →
      HasContainerType heap (.ref address) (.tupleOf element)

  | scalarDictionary {address : Nat} {entries : List (Constant × Value)} {key value : ContainerType} :
      heap[address]? = some (.dict entries) →
      (∀ entry ∈ entries, HasContainerType heap (.scalar entry.1) key) →
      (∀ entry ∈ entries, HasContainerType heap entry.2 value) →
      HasContainerType heap (.ref address) (.dictionary key value)
  | keyedDictionary {address : Nat} {entries : List (HashDict.Entry Value)} {key value : ContainerType} :
      heap[address]? = some (.keyDict entries) →
      (∀ entry ∈ entries, HasContainerType heap entry.2.1 key) →
      (∀ entry ∈ entries, HasContainerType heap entry.2.2 value) →
      HasContainerType heap (.ref address) (.dictionary key value)

theorem Value.HasContainerType.of_heap_preserved
    (typed : Value.HasContainerType heap value kind)
    (preserved : ∀ (address : Nat) (object : Object),
      heap[address]? = some object → other[address]? = some object) :
    Value.HasContainerType other value kind := by
  induction typed with
  | scalar same => exact .scalar same
  | list found _ ih => exact .list (preserved _ _ found) ih
  | fixedTuple found length _ ih => exact .fixedTuple (preserved _ _ found) length ih
  | variadicTuple found _ ih => exact .variadicTuple (preserved _ _ found) ih
  | scalarDictionary found _ _ keys values => exact .scalarDictionary (preserved _ _ found) keys values
  | keyedDictionary found _ _ keys values => exact .keyedDictionary (preserved _ _ found) keys values

theorem Value.HasContainerType.append
    (typed : Value.HasContainerType heap value kind) (extra : Heap) :
    Value.HasContainerType (heap ++ extra) value kind := by
  apply typed.of_heap_preserved
  intro address object found
  have bounded : address < heap.length := by
    by_cases inside : address < heap.length
    · exact inside
    · have missing := List.getElem?_eq_none (Nat.le_of_not_gt inside)
      simp [missing] at found
  rw [List.getElem?_append_left bounded]
  exact found

theorem Value.hasContainerType_list_iff :
    Value.HasContainerType heap (.ref address) (.list element) ↔
      ∃ items, heap[address]? = some (.list items) ∧
        ∀ item ∈ items, Value.HasContainerType heap item element := by
  constructor
  · intro typed
    cases typed with
    | list found elements => exact ⟨_, found, elements⟩
  · rintro ⟨items, found, elements⟩
    exact .list found elements

theorem Value.hasContainerType_tuple_iff :
    Value.HasContainerType heap (.ref address) (.tuple fields) ↔
      ∃ items, heap[address]? = some (.tuple items) ∧ items.length = fields.length ∧
        ∀ pair ∈ items.zip fields, Value.HasContainerType heap pair.1 pair.2 := by
  constructor
  · intro typed
    cases typed with
    | fixedTuple found length elements => exact ⟨_, found, length, elements⟩
  · rintro ⟨items, found, length, elements⟩
    exact .fixedTuple found length elements

theorem Value.hasContainerType_variadicTuple_iff :
    Value.HasContainerType heap (.ref address) (.tupleOf element) ↔
      ∃ items, heap[address]? = some (.tuple items) ∧
        ∀ item ∈ items, Value.HasContainerType heap item element := by
  constructor
  · intro typed
    cases typed with
    | variadicTuple found elements => exact ⟨_, found, elements⟩
  · rintro ⟨items, found, elements⟩
    exact .variadicTuple found elements

theorem Value.hasContainerType_int_iff :
    Value.HasContainerType heap value (.scalar "int") ↔ ∃ n : Int, value = .scalar (.int n) := by
  constructor
  · intro typed
    cases typed with
    | @scalar value same =>
        cases value <;> simp_all [scalarKind, Data.typeName]
  · rintro ⟨n, rfl⟩
    exact .scalar rfl

/-- Recover the two integer fields while retaining their tuple object's address. -/
theorem Value.HasContainerType.int_pair
    (typed : Value.HasContainerType heap (.ref address) (.tuple [.scalar "int", .scalar "int"])) :
    ∃ n d : Int, heap[address]? = some (.tuple [.scalar (.int n), .scalar (.int d)]) := by
  obtain ⟨items, found, length, elements⟩ := Value.hasContainerType_tuple_iff.mp typed
  cases items with
  | nil => simp at length
  | cons first tail =>
      cases tail with
      | nil => simp at length
      | cons second rest =>
          have empty : rest = [] := by
            apply List.length_eq_zero_iff.mp
            simpa using length
          subst rest
          have firstTyped := elements (first, .scalar "int") (by simp)
          have secondTyped := elements (second, .scalar "int") (by simp)
          obtain ⟨n, rfl⟩ := Value.hasContainerType_int_iff.mp firstTyped
          obtain ⟨d, rfl⟩ := Value.hasContainerType_int_iff.mp secondTyped
          exact ⟨n, d, found⟩

namespace Call

def ReturnContainerType (call : Call) (kind : ContainerType) : Prop :=
  call.Throws ∨ ∃ value globals heap anchors,
    call.Finishes ⟨.ok value, globals, heap, anchors⟩ ∧ Value.HasContainerType heap value kind

end Call

namespace CallFamily

def ReturnContainerType (family : CallFamily) (kind : ContainerType) : Prop :=
  ∀ choices, (family.run choices).ReturnContainerType kind

end CallFamily
end FormalSW.PyAst.Mutable
