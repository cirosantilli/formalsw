import lang.py.FormalSW.HeapCalls

/-! Source rules for multi-source set updates and sequential scalar insertion. -/
namespace FormalSW.PyAst.HeapCalls
set_option Elab.async false

private theorem set_same (heap : Heap) (address : Nat) (object : Mutable.Object)
    (found : heap[address]? = some object) : heap.set address object = heap := by
  obtain ⟨inside, entry⟩ := List.getElem?_eq_some_iff.mp found
  rw [← entry, List.set_getElem_self inside]

/-- Inserting a scalar list has no exceptional branch and preserves the original set representatives. -/
theorem addItems_scalars (heap : Heap) (address : Nat) (old items : List Constant)
    (found : heap[address]? = some (.set old)) :
    (items.map Mutable.Value.scalar).mapM (Mutable.addItem address) heap =
      some (.ok (List.replicate items.length (.scalar .none)),
        heap.set address (.set (items.foldl ScalarSet.insert old))) := by
  induction items generalizing heap old with
  | nil => simp [set_same heap address (.set old) found]
  | cons item rest ih =>
    have first : Mutable.addItem address (.scalar item) heap =
        some (.ok (.scalar .none), heap.set address (.set (ScalarSet.insert old item))) := by
      simp [Mutable.addItem, found, Except.map]
    have inserted : (heap.set address (.set (ScalarSet.insert old item)))[address]? =
        some (.set (ScalarSet.insert old item)) := by
      simp [(List.getElem?_eq_some_iff.mp found).1]
    have continued := ih _ _ inserted
    simp only [List.mapM_map] at continued
    simp [List.mapM_cons, Mutable.eval_bind, first, continued, Except.map, List.replicate_succ]

theorem updateSet_list_scalars (heap : Heap) (address source : Nat) (old items : List Constant)
    (destination : heap[address]? = some (.set old))
    (input : heap[source]? = some (.list (items.map Mutable.Value.scalar))) :
    primitive (.updateSet address) [.ref source] heap =
      some (.ok (.scalar .none), heap.set address (.set (items.foldl ScalarSet.insert old))) := by
  simp [primitive, Mutable.updateSet, Mutable.setSourceItems, Mutable.sequence, input,
    Mutable.eval_bind, addItems_scalars heap address old items destination, Except.map]

/-- The receiver is bound before any argument effects; every argument runs before insertion starts. -/
theorem Evaluates.updateSet {globals : Mutable.Globals}
    (receiver : Evaluates (globals := globals) module env base heap (.ref address) middle)
    (original : List (HashKey × Value))
    (found : (middle[address]?).bind Mutable.keyEntries = some original)
    (arguments : Evaluates.Arguments (globals := globals) module env expressions middle values afterArguments)
    (operation : primitive (.updateSet address) values afterArguments = some (.ok value, finalHeap))
    (localName : ∀ name, base = .name name → (env name).isSome = true) :
    Evaluates (globals := globals) module env (.call (.attribute base "update") expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr base env, .methodReceiver "update" expressions env :: stack, heap⟩)
    (by cases base <;> simp_all [step])
  apply (receiver anchors _).trans
  apply Reaches.next (following := argumentsState (.updateSet address) env [] expressions stack middle)
  · cases lookup : middle[address]? with
    | none => simp [lookup] at found
    | some object =>
      cases object <;> simp [lookup, Mutable.keyEntries] at found
      all_goals simp [step, run, bindMethod, lookup]
  · apply (Evaluates.arguments_reach arguments (.updateSet address) [] anchors stack).trans
    exact .next (by simp [step, result, run, operation]) .refl

end FormalSW.PyAst.HeapCalls
