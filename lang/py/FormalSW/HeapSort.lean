import lang.py.FormalSW.MutableGlobals
import lang.py.FormalSW.ScalarSort

/-! Stable sorting retains heap references. List and tuple comparisons inspect equal
prefixes before ordering the first unequal elements, as Python does. -/
namespace FormalSW.PyAst.HeapSort
abbrev Value := Mutable.Value
abbrev Heap := Mutable.Heap

attribute [local simp] bind pure Except.bind Except.map Except.pure

abbrev Result (α : Type) := Option (Except ExceptionObject α)

def typeError : Result α := some (.error { typeName := "TypeError", args := [] })

def lex (equal less : Value → Value → Result Bool) (equality : Bool) :
    List Value → List Value → Result Bool
  | [], [] => some (.ok equality)
  | [], _ :: _ => some (.ok (!equality))
  | _ :: _, [] => some (.ok false)
  | a :: as, b :: bs =>
      match equal a b with
      | none => none
      | some (.error error) => some (.error error)
      | some (.ok true) => lex equal less equality as bs
      | some (.ok false) => if equality then some (.ok false) else less a b

/-- Acyclic sequence nesting uses at most one level per heap object. Exhausting this
heap-derived bound leaves recursive comparisons unsupported. -/
def compare : Nat → Heap → Bool → Value → Value → Result Bool
  | 0, _, _, _, _ => none
  | depth + 1, heap, equality, left, right =>
      match left, right with
      | .scalar a, .scalar b =>
          match scalarCompare (if equality then .eq else .lt) a b with
          | some answer => some (.ok answer)
          | none => typeError
      | .ref a, .ref b =>
          match heap[a]?, heap[b]? with
          | some (.list xs), some (.list ys) | some (.tuple xs), some (.tuple ys) =>
              if equality && a == b then some (.ok true)
              else if equality && xs.length != ys.length then some (.ok false)
              else lex (compare depth heap true) (compare depth heap false) equality xs ys
          | some (.list _), some (.tuple _) | some (.tuple _), some (.list _) =>
              if equality then some (.ok false) else typeError
          | some _, some _ => if equality && a == b then some (.ok true) else none
          | _, _ => none
      | .ref address, .scalar _ | .scalar _, .ref address =>
          match heap[address]? with
          | some (.list _) | some (.tuple _) => if equality then some (.ok false) else typeError
          | _ => none

def insert (heap : Heap) (value : Value) : List Value → Result (List Value)
  | [] => some (.ok [value])
  | first :: rest =>
      match compare (heap.length + 1) heap false first value with
      | none => none
      | some (.error error) => some (.error error)
      | some (.ok true) => (insert heap value rest).map (fun result => result.map (first :: ·))
      | some (.ok false) => some (.ok (value :: first :: rest))

/-- Earlier equal elements stay before later ones, retaining their identities. -/
def sort (heap : Heap) : List Value → Result (List Value)
  | [] => some (.ok [])
  | first :: rest =>
      match sort heap rest with
      | none => none
      | some (.error error) => some (.error error)
      | some (.ok sorted) => insert heap first sorted

theorem insert_scalars (heap : Heap) (value : Constant) (items : List Constant) :
    insert heap (.scalar value) (items.map Mutable.Value.scalar) =
      some ((ScalarSort.insert value items).map (List.map Mutable.Value.scalar)) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, insert, compare, ScalarSort.insert]
      cases order : scalarCompare .lt first value with
      | none => simp [order, typeError, Except.map]
      | some flag =>
          cases flag <;> simp [order, ih, Except.map]
          cases ScalarSort.insert value rest <;> rfl

theorem sort_scalars (heap : Heap) (items : List Constant) :
    sort heap (items.map Mutable.Value.scalar) = some ((ScalarSort.sort items).map (List.map Mutable.Value.scalar)) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, sort, ih, ScalarSort.sort]
      cases ordered : ScalarSort.sort rest <;> simp [insert_scalars, Except.map]

def lexInt : List Int → List Int → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then lexInt as bs else decide (a < b)

theorem lex_ints (heap : Heap) (depth : Nat) (xs ys : List Int) :
    lex (compare (depth + 1) heap true) (compare (depth + 1) heap false) false
      (xs.map fun n => .scalar (.int n)) (ys.map fun n => .scalar (.int n)) = some (.ok (lexInt xs ys)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          have equal : compare (depth + 1) heap true (.scalar (.int x)) (.scalar (.int y)) =
              some (.ok (decide (x = y))) := rfl
          have less : compare (depth + 1) heap false (.scalar (.int x)) (.scalar (.int y)) =
              some (.ok (decide (x < y))) := rfl
          simp only [List.map_cons, lex, equal]
          by_cases same : x = y <;> simp [less, lexInt, same, ih]

theorem compare_int_lists (heap : Heap) (a b depth : Nat) (xs ys : List Int)
    (left : heap[a]? = some (.list (xs.map fun n => .scalar (.int n))))
    (right : heap[b]? = some (.list (ys.map fun n => .scalar (.int n)))) :
    compare (depth + 2) heap false (.ref a) (.ref b) = some (.ok (lexInt xs ys)) := by
  simpa [compare, left, right] using lex_ints heap depth xs ys

/-- Integer tuples use the same lexicographic order as integer lists. -/
theorem compare_int_tuples (heap : Heap) (a b depth : Nat) (xs ys : List Int)
    (left : heap[a]? = some (.tuple (xs.map fun n => .scalar (.int n))))
    (right : heap[b]? = some (.tuple (ys.map fun n => .scalar (.int n)))) :
    compare (depth + 2) heap false (.ref a) (.ref b) = some (.ok (lexInt xs ys)) := by
  simpa [compare, left, right] using lex_ints heap depth xs ys

def insertBy (less : α → α → Bool) (value : α) : List α → List α
  | [] => [value]
  | first :: rest => if less first value then first :: insertBy less value rest else value :: first :: rest

def sortBy (less : α → α → Bool) : List α → List α
  | [] => []
  | first :: rest => insertBy less first (sortBy less rest)

/-- Mapping values commutes with insertion when comparisons use the mapped values. -/
theorem insertBy_map (f : α → β) (less : β → β → Bool) (value : α) (items : List α) :
    (insertBy (fun a b => less (f a) (f b)) value items).map f =
      insertBy less (f value) (items.map f) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      cases compared : less (f first) (f value) <;> simp [insertBy, compared, ih]

/-- Sort references by their contents, then project the sorted contents. -/
theorem sortBy_map (f : α → β) (less : β → β → Bool) (items : List α) :
    (sortBy (fun a b => less (f a) (f b)) items).map f = sortBy less (items.map f) := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp [sortBy, insertBy_map, ih]

theorem insertBy_perm (less : α → α → Bool) (value : α) (items : List α) :
    (insertBy less value items).Perm (value :: items) := by
  induction items with
  | nil => exact .refl _
  | cons first rest ih =>
      cases comparison : less first value with
      | false => simp [insertBy, comparison]
      | true => simpa [insertBy, comparison] using (ih.cons first).trans (.swap _ _ _)

theorem sortBy_perm (less : α → α → Bool) (items : List α) : (sortBy less items).Perm items := by
  induction items with
  | nil => exact .refl _
  | cons first rest ih => exact (insertBy_perm less first _).trans (ih.cons first)

theorem insert_of_compare (heap : Heap) (less : Value → Value → Bool) (value : Value) (items : List Value)
    (comparisons : ∀ item ∈ items, compare (heap.length + 1) heap false item value = some (.ok (less item value))) :
    insert heap value items = some (.ok (insertBy less value items)) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      have firstCompared := comparisons first List.mem_cons_self
      have tailCompared := ih (fun item member => comparisons item (List.mem_cons_of_mem _ member))
      simp [insert, firstCompared, insertBy, tailCompared]
      cases less first value <;> rfl

theorem sort_of_compare (heap : Heap) (less : Value → Value → Bool) (items : List Value)
    (comparisons : ∀ left ∈ items, ∀ right ∈ items,
      compare (heap.length + 1) heap false left right = some (.ok (less left right))) :
    sort heap items = some (.ok (sortBy less items)) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      have tailCompared := ih (fun left hl right hr =>
        comparisons left (List.mem_cons_of_mem _ hl) right (List.mem_cons_of_mem _ hr))
      simp only [sort, tailCompared, sortBy]
      apply insert_of_compare
      intro item member
      exact comparisons item (List.mem_cons_of_mem _ ((sortBy_perm less rest).mem_iff.mp member))
        first List.mem_cons_self

/-- Total projection used only under proofs that the row contains integers. -/
def readInts (heap : Heap) : Value → List Int
  | .ref address => match heap[address]? with
      | some (.list items) => items.filterMap fun value => match value with
          | .scalar (.int n) => some n
          | _ => none
      | _ => []
  | _ => []

theorem sort_int_lists (heap : Heap) (addresses : List Nat)
    (typed : ∀ address ∈ addresses, Mutable.Value.HasType heap (.ref address) "list[int]") :
    sort heap (addresses.map Mutable.Value.ref) =
      some (.ok (sortBy (fun left right => lexInt (readInts heap left) (readInts heap right))
        (addresses.map Mutable.Value.ref))) := by
  apply sort_of_compare
  intro left leftMember right rightMember
  obtain ⟨a, aMember, rfl⟩ := List.mem_map.mp leftMember
  obtain ⟨b, bMember, rfl⟩ := List.mem_map.mp rightMember
  obtain ⟨xs, aFound⟩ := Mutable.Value.ints_of_hasType (typed a aMember)
  obtain ⟨ys, bFound⟩ := Mutable.Value.ints_of_hasType (typed b bMember)
  have positive : 0 < heap.length := by
    by_cases nonempty : 0 < heap.length
    · exact nonempty
    · have bound : heap.length ≤ a := by omega
      rw [List.getElem?_eq_none bound] at aFound
      cases aFound
  have depth : heap.length - 1 + 2 = heap.length + 1 := by omega
  have compared := compare_int_lists heap a b (heap.length - 1) xs ys aFound bFound
  simpa [depth, readInts, aFound, bFound, List.filterMap_map, Function.comp_def] using compared

end FormalSW.PyAst.HeapSort
