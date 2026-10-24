import lang.py.FormalSW.GeneratorCalls

/-! Reverse sorting preserves equal elements' input order and their references. -/
namespace FormalSW.PyAst.HeapCalls

def sortedInts (reverse : Bool) (items : List Int) : List Int :=
  if reverse then (ScalarSort.ints items.reverse).reverse else ScalarSort.ints items

private abbrev numbers (items : List Int) : List Value :=
  (items.map Constant.int).map Mutable.Value.scalar

theorem sortWithReverse_ints (heap : Heap) (reverse : Bool) (items : List Int) :
    HeapSort.sortWithReverse heap reverse (numbers items) = some (.ok (numbers (sortedInts reverse items))) := by
  have ascending (values : List Int) : HeapSort.sort heap (numbers values) = some (.ok (numbers (ScalarSort.ints values))) := by
    simpa only [ScalarSort.sort_ints, Except.map] using HeapSort.sort_scalars heap (values.map Constant.int)
  cases reverse with
  | false => exact ascending items
  | true =>
      have reversed : (numbers items).reverse = numbers items.reverse := by simp [numbers, List.map_reverse]
      simp only [HeapSort.sortWithReverse, ↓reduceIte, reversed, ascending, Option.map_some, Except.map]
      simp [sortedInts, numbers, List.map_reverse]

theorem primitive_sorted_reverse_list (heap : Heap) (address : Nat) (items sorted : List Value) (reverse : Bool)
    (found : heap[address]? = some (.list items))
    (ordered : HeapSort.sortWithReverse heap reverse items = some (.ok sorted)) :
    primitive (.builtin .sortedReverse) [.ref address, .scalar (.bool reverse)] heap =
      some (.ok (.ref heap.length), heap ++ [.list sorted]) := by
  simp [primitive, found, Mutable.sequence, Mutable.truth, scalarTruth, ordered, Mutable.allocate, Except.map]

theorem primitive_sort_reverse_ints (heap : Heap) (address : Nat) (items : List Int) (reverse : Bool)
    (found : heap[address]? = some (.list (numbers items))) :
    primitive (.sortReverse address) [.scalar (.bool reverse)] heap =
      some (.ok (.scalar .none), heap.set address (.list (numbers (sortedInts reverse items)))) := by
  have ordered : HeapSort.sortWithReverse heap reverse (items.map (Mutable.Value.scalar ∘ Constant.int)) =
      some (.ok ((sortedInts reverse items).map (Mutable.Value.scalar ∘ Constant.int))) := by
    simpa only [numbers, List.map_map] using sortWithReverse_ints heap reverse items
  simp [primitive, found, Mutable.truth, scalarTruth, ordered]
  split
  · rename_i bad
    obtain ⟨value, member, impossible⟩ := bad
    obtain ⟨item, _, rfl⟩ := List.mem_map.mp member
    cases impossible
  · rfl

/-- Capture the list method before evaluating the keyword expression. -/
theorem Evaluates.sort_reverse
    (receiver : Evaluates (globals := globals) module env base heap (.ref address) middle)
    (found : middle[address]? = some (.list items))
    (argument : Evaluates (globals := globals) module env expression middle reverse afterArgument)
    (operation : primitive (.sortReverse address) [reverse] afterArgument = some (.ok (.scalar .none), finalHeap))
    (localName : ∀ name, base = .name name → (env name).isSome = true) :
    Evaluates (globals := globals) module env (.call (.attribute base "$formalsw.sort.reverse") [expression])
      heap (.scalar .none) finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr base env, .methodReceiver "$formalsw.sort.reverse" [expression] env :: stack, heap⟩)
    (by cases base <;> simp_all [step])
  apply (receiver anchors _).trans
  apply Reaches.next (following := argumentsState (.sortReverse address) env [] [expression] stack middle)
    (by simp [step, run, bindMethod, found])
  apply (Evaluates.arguments_reach (.cons argument .nil) (.sortReverse address) [] anchors stack).trans
  exact .next (by simp [step, result, run, operation]) .refl

end FormalSW.PyAst.HeapCalls
