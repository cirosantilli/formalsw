import «.cleanxy».tests.py.«parallel_doubly_linked_list.py.ast»
import CleanXY
open CleanXY.PyAst

namespace DoublyLinked
-- Heap identities: 0 = HEAD, 1 = TAIL, 2 and 3 = the inserted nodes.
def node (prev next : SharedValue) : SharedObject := .object [("prev", prev), ("next", next)]
def initial : SharedState :=
  { objects := [node .none (.ref 1), node (.ref 0) .none, node .none .none, node .none .none] }

-- HEAD.next is node 3, yet TAIL.prev is node 2: the reachable chain disagrees.
def broken : SharedState :=
  { objects := [node .none (.ref 3), node (.ref 2) .none,
      node (.ref 0) (.ref 1), node (.ref 0) (.ref 1)] }

def reciprocal (state : SharedState) (address : Nat) (forward backward : String) : Bool :=
  match state.field address forward with
  | some .none => true
  | some (.ref other) => state.field other backward == some (.ref address)
  | _ => false

def linksAgree (state : SharedState) : Prop :=
  (List.range state.objects.length).all (fun address =>
    reciprocal state address "next" "prev" && reciprocal state address "prev" "next") = true

def chain (state : SharedState) (addresses : List Nat) : Bool :=
  (addresses.zip addresses.tail).all fun (left, right) =>
    state.field left "next" == some (.ref right) && state.field right "prev" == some (.ref left)

-- Both nodes must be reachable in either order; sentinels and reciprocal links agree.
def valid (state : SharedState) : Prop :=
  linksAgree state ∧ (chain state [0, 2, 3, 1] || chain state [0, 3, 2, 1]) = true ∧
    state.field 0 "prev" = some .none ∧ state.field 1 "next" = some .none

instance (state : SharedState) : Decidable (linksAgree state) := inferInstanceAs (Decidable (_ = true))
instance (state : SharedState) : Decidable (valid state) :=
  inferInstanceAs (Decidable (linksAgree state ∧ _ ∧ _ ∧ _))

theorem broken_links : ¬ linksAgree broken := by decide
end DoublyLinked

namespace tests.py.parallel_doubly_linked_list
private def calls (name : String) :=
  [parallelFunction ParallelDoublyLinkedListAst.module name [.ref 0, .ref 2, .lock 0],
   parallelFunction ParallelDoublyLinkedListAst.module name [.ref 0, .ref 3, .lock 0]]

theorem insert_safe.preserves_list :
    Ensures(Parallel(calls "insert_safe", DoublyLinked.initial), DoublyLinked.valid) := by
  native_decide

theorem insert_unsafe.can_corrupt_links :
    CanReturn(Parallel(calls "insert_unsafe", DoublyLinked.initial), DoublyLinked.broken) := by
  native_decide

theorem insert_unsafe.links_not_guaranteed :
    Not Ensures(Parallel(calls "insert_unsafe", DoublyLinked.initial), DoublyLinked.linksAgree) := by
  intro guarantee
  exact DoublyLinked.broken_links (guarantee.of_canReturn insert_unsafe.can_corrupt_links)

-- Both read TAIL. Node 3 wins the HEAD.next write, but node 2 wins TAIL.prev.
theorem insert_unsafe.corrupting_schedule :
    ((calls "insert_unsafe").mapM id).map (fun workers =>
      parallelReplay ⟨DoublyLinked.initial, workers⟩ [0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0]) =
      some (.ok DoublyLinked.broken) := by
  native_decide
end tests.py.parallel_doubly_linked_list
