import «.cleanxy».tests.py.«mutable_globals.py.ast»
import CleanXY

set_option linter.unusedSimpArgs false

open CleanXY.PyAst
open CleanXY.PyAst.Mutable

namespace tests.py.mutable_globals

private abbrev call (name : String) (n : Int) (address : Nat) (heap : Heap) :=
  Mutable.function MutableGlobalsAst.module name [.scalar (.int n)] [("items", .ref address)] heap

private theorem push_done (heap : Heap) (address : Nat) (items : List Mutable.Value) (n : Int)
    (found : heap[address]? = some items) :
    (call "push" n address heap).Finishes
      ⟨.ok (.scalar .none), [("items", .ref address)], heap.set address (items ++ [.scalar (.int n)]), heap.length⟩ := by
  apply Call.finishes_of_observe (fuel := 2)
  simp [call, Mutable.function, MutableGlobalsAst.module, findFunctionIn,
    blockGlobals, declaredGlobals, blockLocals, assignedLocals, executableBody,
    Execution.observe, Execution.observeFrom, step, expr, array, completion, Except.map, List.lookup,  found]

private theorem alias_done (heap : Heap) (address : Nat) (items : List Mutable.Value) (n : Int)
    (found : heap[address]? = some items) :
    (call "push_via_alias" n address heap).Finishes
      ⟨.ok (.scalar .none), [("items", .ref address)], heap.set address (items ++ [.scalar (.int n)]), heap.length⟩ := by
  apply Call.finishes_of_observe (fuel := 3)
  simp [call, Mutable.function, MutableGlobalsAst.module, findFunctionIn,
    blockGlobals, declaredGlobals, blockLocals, assignedLocals, executableBody,
    Execution.observe, Execution.observeFrom, step, expr, array, assign, completion,
    Except.map, List.lookup,  found]

private theorem raise_done (heap : Heap) (address : Nat) (items : List Mutable.Value) (n : Int)
    (found : heap[address]? = some items) :
    (call "push_then_raise" n address heap).Finishes
      ⟨.error ⟨"ValueError", [.string "failure"]⟩, [("items", .ref address)],
        heap.set address (items ++ [.scalar (.int n)]), heap.length⟩ := by
  apply Call.finishes_of_observe (fuel := 2)
  simp [call, Mutable.function, MutableGlobalsAst.module, findFunctionIn,
    blockGlobals, declaredGlobals, blockLocals, assignedLocals, executableBody,
    Execution.observe, Execution.observeFrom, step, expr, array, assign, completion,
    Except.map, List.lookup,  found]

private theorem replace_done (heap : Heap) (address : Nat) (items : List Mutable.Value) (n : Int)
    (found : heap[address]? = some items) :
    (call "replace" n address heap).Finishes
      ⟨.ok (.scalar .none), [("items", .ref (heap.length + 1))],
        heap ++ [[.scalar (.int n)]] ++ [items ++ [.scalar (.int n)]], heap.length⟩ := by
  have lt := (List.getElem?_eq_some_iff.mp found).1
  have add : (BinOp.add == BinOp.add) = true := rfl
  apply Call.finishes_of_observe (fuel := 3)
  simp [call, Mutable.function, MutableGlobalsAst.module, findFunctionIn,
    blockGlobals, declaredGlobals, blockLocals, assignedLocals, executableBody,
    Execution.observe, Execution.observeFrom, step, expr, array, assign, completion,
    Except.map, List.lookup,  found, binary, allocate, List.getElem?_append, lt, add]
  exact (List.getElem?_eq_some_iff.mp found).2

private theorem empty_valid : Heap.Valid [[]] := by simp [Heap.Valid]
private theorem empty_ints : Mutable.Value.HasType [[]] (.ref 0) "list[int]" := by
  exact ⟨[], rfl, Or.inr ⟨"int", rfl, by simp⟩⟩

theorem push.«Returns» :
    ∀ (heap : CleanXY.PyAst.Mutable.Heap) (n : Int) (items : Nat),
    (CleanXY.PyAst.Mutable.Heap.Valid heap) → (CleanXY.PyAst.Mutable.Value.HasType heap (.ref items) "list[int]") →
    (CleanXY.PyAst.Mutable.function MutableGlobalsAst.module "push" [.scalar (.int n)] [("items", .ref items)] heap).Returns
  := by
  intro heap n address _ typed
  obtain ⟨items, found, _⟩ := typed
  exact ⟨_, _, _, _, push_done heap address items n found⟩

theorem push.«Halts» :
    ∀ (heap : CleanXY.PyAst.Mutable.Heap) (n : Int) (items : Nat),
    (CleanXY.PyAst.Mutable.Heap.Valid heap) → (CleanXY.PyAst.Mutable.Value.HasType heap (.ref items) "list[int]") →
    (CleanXY.PyAst.Mutable.function MutableGlobalsAst.module "push" [.scalar (.int n)] [("items", .ref items)] heap).Halts
  := by
  intro heap n address valid typed
  exact ((Call.returns_iff_halts_not_throws _).mp (push.«Returns» heap n address valid typed)).1

theorem push.«Not Throws» :
    Not (∃ (heap : CleanXY.PyAst.Mutable.Heap) (n : Int) (items : Nat),
    (CleanXY.PyAst.Mutable.Heap.Valid heap) ∧ (CleanXY.PyAst.Mutable.Value.HasType heap (.ref items) "list[int]") ∧ ((CleanXY.PyAst.Mutable.function MutableGlobalsAst.module "push" [.scalar (.int n)] [("items", .ref items)] heap).Throws))
  := by
  rintro ⟨heap, n, address, valid, typed, thrown⟩
  exact ((Call.returns_iff_halts_not_throws _).mp (push.«Returns» heap n address valid typed)).2 thrown

theorem push.«ReturnType» :
    ∀ (heap : CleanXY.PyAst.Mutable.Heap) (n : Int) (items : Nat),
    (CleanXY.PyAst.Mutable.Heap.Valid heap) → (CleanXY.PyAst.Mutable.Value.HasType heap (.ref items) "list[int]") →
    (CleanXY.PyAst.Mutable.function MutableGlobalsAst.module "push" [.scalar (.int n)] [("items", .ref items)] heap).ReturnType "None"
  := by
  intro heap n address _ typed
  obtain ⟨items, found, _⟩ := typed
  exact Or.inr ⟨_, _, _, _, push_done heap address items n found, rfl⟩

theorem push_via_alias.«Equiv(push)» :
    ∀ (heap : CleanXY.PyAst.Mutable.Heap) (n : Int) (items : Nat),
    (CleanXY.PyAst.Mutable.Heap.Valid heap) → (CleanXY.PyAst.Mutable.Value.HasType heap (.ref items) "list[int]") →
    (CleanXY.PyAst.Mutable.function MutableGlobalsAst.module "push_via_alias" [.scalar (.int n)] [("items", .ref items)] heap).Equiv (CleanXY.PyAst.Mutable.function MutableGlobalsAst.module "push" [.scalar (.int n)] [("items", .ref items)] heap)
  := by
  intro heap n address _ typed
  obtain ⟨items, found, _⟩ := typed
  exact Call.equiv_of_finishes (alias_done heap address items n found)
    (push_done heap address items n found) (Or.inl rfl)

theorem replace.«Returns» :
    ∀ (heap : CleanXY.PyAst.Mutable.Heap) (n : Int) (items : Nat),
    (CleanXY.PyAst.Mutable.Heap.Valid heap) → (CleanXY.PyAst.Mutable.Value.HasType heap (.ref items) "list[int]") →
    (CleanXY.PyAst.Mutable.function MutableGlobalsAst.module "replace" [.scalar (.int n)] [("items", .ref items)] heap).Returns
  := by
  intro heap n address _ typed
  obtain ⟨items, found, _⟩ := typed
  exact ⟨_, _, _, _, replace_done heap address items n found⟩

theorem replace.«Not Equiv(push)» :
    Not (∀ (heap : CleanXY.PyAst.Mutable.Heap) (n : Int) (items : Nat),
    (CleanXY.PyAst.Mutable.Heap.Valid heap) → (CleanXY.PyAst.Mutable.Value.HasType heap (.ref items) "list[int]") →
    (CleanXY.PyAst.Mutable.function MutableGlobalsAst.module "replace" [.scalar (.int n)] [("items", .ref items)] heap).Equiv (CleanXY.PyAst.Mutable.function MutableGlobalsAst.module "push" [.scalar (.int n)] [("items", .ref items)] heap))
  := by
  intro all
  obtain ⟨result, done, eq⟩ := (all [[]] 1 0 empty_valid empty_ints).1 _ (replace_done [[]] 0 [] 1 rfl)
  have actual := Call.unique done (push_done [[]] 0 [] 1 rfl)
  subst result
  rcases eq with exact | ⟨_, _, _, graph⟩
  · cases exact
  · exact (Graph.not_equivalent_of_observe (fuel := 1000) (by native_decide)) graph

theorem push_then_raise.«Halts» :
    ∀ (heap : CleanXY.PyAst.Mutable.Heap) (n : Int) (items : Nat),
    (CleanXY.PyAst.Mutable.Heap.Valid heap) → (CleanXY.PyAst.Mutable.Value.HasType heap (.ref items) "list[int]") →
    (CleanXY.PyAst.Mutable.function MutableGlobalsAst.module "push_then_raise" [.scalar (.int n)] [("items", .ref items)] heap).Halts
  := by
  intro heap n address _ typed
  obtain ⟨items, found, _⟩ := typed
  exact ⟨_, raise_done heap address items n found⟩

theorem push_then_raise.«Throws» :
    ∃ (heap : CleanXY.PyAst.Mutable.Heap) (n : Int) (items : Nat),
    (CleanXY.PyAst.Mutable.Heap.Valid heap) ∧ (CleanXY.PyAst.Mutable.Value.HasType heap (.ref items) "list[int]") ∧ ((CleanXY.PyAst.Mutable.function MutableGlobalsAst.module "push_then_raise" [.scalar (.int n)] [("items", .ref items)] heap).Throws)
  := by
  exact ⟨[[]], 1, 0, empty_valid, empty_ints, _, _, _, _, raise_done [[]] 0 [] 1 rfl⟩

theorem push_then_raise.«Not Equiv(raise_without_push)» :
    Not (∀ (heap : CleanXY.PyAst.Mutable.Heap) (n : Int) (items : Nat),
    (CleanXY.PyAst.Mutable.Heap.Valid heap) → (CleanXY.PyAst.Mutable.Value.HasType heap (.ref items) "list[int]") →
    (CleanXY.PyAst.Mutable.function MutableGlobalsAst.module "push_then_raise" [.scalar (.int n)] [("items", .ref items)] heap).Equiv (CleanXY.PyAst.Mutable.function MutableGlobalsAst.module "raise_without_push" [.scalar (.int n)] [("items", .ref items)] heap))
  := by
  intro all
  obtain ⟨result, done, eq⟩ := (all [[]] 1 0 empty_valid empty_ints).1 _ (raise_done [[]] 0 [] 1 rfl)
  have before : (call "raise_without_push" 1 0 [[]]).Finishes
      ⟨.error ⟨"ValueError", [.string "failure"]⟩, [("items", .ref 0)], [[]], 1⟩ :=
    Call.finishes_of_observe (fuel := 1) (by native_decide)
  have actual := Call.unique done before
  subst result
  rcases eq with exact | ⟨_, _, _, graph⟩
  · cases exact
  · exact (Graph.not_equivalent_of_observe (fuel := 1000) (by native_decide)) graph

theorem read_first.«Throws» :
    ∃ (heap : CleanXY.PyAst.Mutable.Heap) (n : Int) (items : Nat),
    (CleanXY.PyAst.Mutable.Heap.Valid heap) ∧ (CleanXY.PyAst.Mutable.Value.HasType heap (.ref items) "list[int]") ∧ ((CleanXY.PyAst.Mutable.function MutableGlobalsAst.module "read_first" [.scalar (.int n)] [("items", .ref items)] heap).Throws)
  := by
  refine ⟨[[]], 1, 0, empty_valid, empty_ints, ⟨"IndexError", []⟩, [("items", .ref 0)], [[]], 1, ?_⟩
  exact Call.finishes_of_observe (fuel := 1) (by native_decide)

theorem push_argument.«Returns» :
    ∀ (heap : CleanXY.PyAst.Mutable.Heap) (other : Nat) (n : Int) (items : Nat),
    (CleanXY.PyAst.Mutable.Heap.Valid heap) → (CleanXY.PyAst.Mutable.Value.HasType heap (.ref other) "list[int]") → (CleanXY.PyAst.Mutable.Value.HasType heap (.ref items) "list[int]") →
    (CleanXY.PyAst.Mutable.function MutableGlobalsAst.module "push_argument" [.ref other, .scalar (.int n)] [("items", .ref items)] heap).Returns
  := by
  intro heap other n address _ otherTyped typed
  obtain ⟨otherItems, otherFound, _⟩ := otherTyped
  obtain ⟨items, found, _⟩ := typed
  have lt := (List.getElem?_eq_some_iff.mp found).1
  have lookup : ∃ updated, (heap.set other (otherItems ++ [.scalar (.int n)]))[address]? = some updated := by
    have otherLt := (List.getElem?_eq_some_iff.mp otherFound).1
    simp only [List.getElem?_set, if_pos otherLt]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨items, found⟩
  obtain ⟨updated, updatedFound⟩ := lookup
  refine ⟨.scalar (.int updated.length), [("items", .ref address)],
    heap.set other (otherItems ++ [.scalar (.int n)]), heap.length, ?_⟩
  apply Call.finishes_of_observe (fuel := 2)
  simp [Mutable.function, MutableGlobalsAst.module, findFunctionIn,
    blockGlobals, declaredGlobals, blockLocals, assignedLocals, executableBody,
    Execution.observe, Execution.observeFrom, step, expr, array, assign, completion,
    Except.map, List.lookup,  otherFound, updatedFound]

theorem push.returns_on_heap :
    let _this_module := MutableGlobalsAst.module;
    ∀ (heap : Mutable.Heap) (n : Int) (items : Nat),
    let this_function := fun (input_0 : Int) =>
      Mutable.function MutableGlobalsAst.module "push" [.scalar (.int input_0)] [("items", .ref items)] heap;
    Mutable.Heap.Valid heap → Mutable.Value.HasType heap (.ref items) "list[int]" →
      Returns(this_function(n)) := push.«Returns»

theorem push_via_alias.«EquivReturn(push)» (heap : Heap) (n : Int) (items : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref items) "list[int]") :
    (call "push_via_alias" n items heap).EquivReturn (call "push" n items heap) :=
  (push_via_alias.«Equiv(push)» heap n items valid typed).equivReturn

end tests.py.mutable_globals
