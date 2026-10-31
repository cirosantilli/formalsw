import lang.py.FormalSW.HeapCalls

namespace FormalSW.PyAst.Heapq

attribute [local simp] Except.map

theorem items_list (heap : Heap) (address : Nat) (values : List Value)
    (found : heap[address]? = some (.list values)) :
    items address heap = some (.ok values, heap) := by
  simp [items, found]

theorem receiver_list (heap : Heap) (address : Nat) (values : List Value)
    (found : heap[address]? = some (.list values)) :
    receiver (.ref address) heap = some (.ok address, heap) := by
  simp [receiver, items_list heap address values found]

theorem atIndex_list (heap : Heap) (address position : Nat) (values : List Value)
    (found : heap[address]? = some (.list values)) (valid : position < values.length) :
    atIndex address position heap = some (.ok values[position], heap) := by
  simp [atIndex, items_list heap address values found, valid]

theorem swap_list (heap : Heap) (address left right : Nat) (values : List Value)
    (found : heap[address]? = some (.list values))
    (leftValid : left < values.length) (rightValid : right < values.length) :
    swap address left right heap = some (.ok (),
      heap.set address (.list ((values.set left values[right]).set right values[left]))) := by
  simp [swap, items_list heap address values found, leftValid, rightValid]

theorem less_int (heap : Heap) (left right : Int) :
    less (.scalar (.int left)) (.scalar (.int right)) heap =
      some (.ok (decide (left < right)), heap) := rfl

theorem less_string (heap : Heap) (left right : String) :
    less (.scalar (.string left)) (.scalar (.string right)) heap =
      some (.ok (decide (left < right)), heap) := rfl

theorem siftDown_stop (heap : Heap) (address start position : Nat)
    (stopped : position ≤ start) :
    siftDown address start position heap = some (.ok (), heap) := by
  rw [siftDown]
  simp [Nat.not_lt.mpr stopped]

/-- Expose a successful push's sift without losing its prior append on errors. -/
theorem heappush_result (heap after : Heap) (address : Nat) (values : List Value)
    (item : Value) (outcome : Except ExceptionObject Unit)
    (found : heap[address]? = some (.list values))
    (sifted : siftDown address 0 values.length
      (heap.set address (.list (values ++ [item]))) = some (outcome, after)) :
    heappush [.ref address, item] heap =
      some (outcome.map (fun _ => .scalar .none), after) := by
  cases outcome <;>
    simp [heappush, receiver_list heap address values found,
      items_list heap address values found, Mutable.appendItem, found, sifted]

/-- The traversal is finite by construction and depends only on the list size. -/
theorem heapify_result (heap after : Heap) (address : Nat) (values : List Value)
    (outcome : Except ExceptionObject Unit)
    (found : heap[address]? = some (.list values))
    (sifted : siftAll address (heapifyOrder values.length) heap = some (outcome, after)) :
    heapify [.ref address] heap = some (outcome.map (fun _ => .scalar .none), after) := by
  cases outcome <;>
    simp [heapify, receiver_list heap address values found,
      items_list heap address values found, sifted]

/-- A failed pop retains its already shortened list and root replacement. -/
theorem heappop_result (heap shortened after : Heap) (address : Nat) (values rest : List Value)
    (last root : Value) (outcome : Except ExceptionObject Unit)
    (found : heap[address]? = some (.list values))
    (popped : Mutable.popItem address (.scalar (.int (-1))) heap = some (.ok last, shortened))
    (remaining : shortened[address]? = some (.list (root :: rest)))
    (sifted : siftUp address 0 (shortened.set address (.list (last :: rest))) =
      some (outcome, after)) :
    heappop [.ref address] heap = some (outcome.map (fun _ => root), after) := by
  cases outcome <;>
    simp [heappop, receiver_list heap address values found, popped,
      items_list shortened address (root :: rest) remaining, sifted]

theorem heappush_empty (heap : Heap) (address : Nat) (item : Value)
    (found : heap[address]? = some (.list [])) :
    heappush [.ref address, item] heap =
      some (.ok (.scalar .none), heap.set address (.list [item])) := by
  apply heappush_result heap _ address [] item (.ok ()) found
  exact siftDown_stop _ address 0 0 (Nat.le_refl 0)

theorem heapify_singleton (heap : Heap) (address : Nat) (item : Value)
    (found : heap[address]? = some (.list [item])) :
    heapify [.ref address] heap = some (.ok (.scalar .none), heap) := by
  apply heapify_result heap heap address [item] (.ok ()) found
  simp [heapifyOrder, siftAll]

theorem heappop_singleton (heap : Heap) (address : Nat) (item : Value)
    (found : heap[address]? = some (.list [item])) :
    heappop [.ref address] heap = some (.ok item, heap.set address (.list [])) := by
  have valid := (List.getElem?_eq_some_iff.mp found).1
  have popped : Mutable.popItem address (.scalar (.int (-1))) heap =
      some (.ok item, heap.set address (.list [])) := by
    simp only [Mutable.popItem, Mutable.integer, Mutable.eval_bind,
      Mutable.eval_pure, Mutable.eval_get, Option.bind_eq_bind, Option.bind_some, found]
    rfl
  simp [heappop, receiver_list heap address [item] found, popped, items, valid]

end FormalSW.PyAst.Heapq

namespace FormalSW.PyAst.HeapCalls

theorem primitive_heapq_heapify (values : List Value) :
    primitive (.builtin .heapqHeapify) values = Heapq.heapify values := rfl

theorem primitive_heapq_push (values : List Value) :
    primitive (.builtin .heapqPush) values = Heapq.heappush values := rfl

theorem primitive_heapq_pop (values : List Value) :
    primitive (.builtin .heapqPop) values = Heapq.heappop values := rfl

end FormalSW.PyAst.HeapCalls
