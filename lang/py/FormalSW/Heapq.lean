import lang.py.FormalSW.HeapSort

/-! The three min-heap operations in CPython's `_heapq` module. Comparisons use
the supported builtin values; custom comparison hooks remain unsupported.
Swaps and partial updates follow the C implementation, including on exceptions.
See https://github.com/python/cpython/blob/3.14/Modules/_heapqmodule.c. -/
namespace FormalSW.PyAst.Heapq

abbrev Value := Mutable.Value
abbrev Heap := Mutable.Heap
abbrev Eval := Mutable.Eval

def items (address : Nat) : Eval (List Value) := do
  match (← get)[address]? with
  | some (.list values) => return values
  | some _ => Mutable.error "TypeError"
  | none => Mutable.unsupported

def receiver : Value → Eval Nat
  | .ref address => do
      let _ ← items address
      return address
  | .scalar _ => Mutable.error "TypeError"

def atIndex (address position : Nat) : Eval Value := do
  match (← items address)[position]? with
  | some value => return value
  | none => Mutable.error "IndexError"

def swap (address left right : Nat) : Eval Unit := do
  let values ← items address
  match values[left]?, values[right]? with
  | some a, some b =>
      modify fun heap => heap.set address (.list ((values.set left b).set right a))
  | _, _ => Mutable.error "IndexError"

def less (left right : Value) : Eval Bool := do
  let heap ← get
  match HeapSort.compare (HeapSort.comparisonFuel heap) heap false left right with
  | some (.ok answer) => return answer
  | some (.error exception) => throw exception
  | none => Mutable.unsupported

/-- Move the item towards the root, stopping at its original subtree root. -/
def siftDown (address start position : Nat) : Eval Unit := do
  if start < position then
    let parent := (position - 1) / 2
    let value ← atIndex address position
    let above ← atIndex address parent
    if ← less value above then
      swap address position parent
      siftDown address start parent
termination_by position
decreasing_by
  have := Nat.div_le_self (position - 1) 2
  omega

/-- Move the smaller child upwards, then restore the displaced item's position.
Equal children select the right child, retaining the observable heap layout. -/
def siftChildren (address size start position : Nat) : Eval Unit := do
  let left := 2 * position + 1
  if left < size then
    let right := left + 1
    if right < size then
      let a ← atIndex address left
      let b ← atIndex address right
      if ← less a b then
        swap address position left
        siftChildren address size start left
      else
        swap address position right
        siftChildren address size start right
    else
      swap address position left
      siftChildren address size start left
  else
    siftDown address start position
termination_by size - position
decreasing_by all_goals omega

def siftUp (address position : Nat) : Eval Unit := do
  let values ← items address
  if position < values.length then
    siftChildren address values.length position position
  else Mutable.error "IndexError"

/-- Cache traversal visits a parent immediately after its rightmost child. -/
def parentPath (position : Nat) : List Nat :=
  position :: if position % 2 = 1 then parentPath (position / 2) else []
termination_by position
decreasing_by
  apply Nat.div_lt_self <;> omega

def descending (start count : Nat) : List Nat :=
  (List.range count).reverse.map (start + ·)

/-- The cache threshold changes traversal order, never the input domain. -/
def heapifyOrder (size : Nat) : List Nat :=
  if size > 2500 then
    let firstLeaf := size / 2
    let leftmost := 2 ^ Nat.log2 (firstLeaf + 1) - 1
    let half := firstLeaf / 2
    ((descending half (leftmost - half)) ++
      (descending leftmost (firstLeaf - leftmost))).flatMap parentPath
  else
    (List.range (size / 2)).reverse

def siftAll (address : Nat) : List Nat → Eval Unit
  | [] => pure ()
  | position :: rest => do
      siftUp address position
      siftAll address rest

def heapify : List Value → Eval Value
  | [value] => do
      let address ← receiver value
      siftAll address (heapifyOrder (← items address).length)
      return .scalar .none
  | _ => Mutable.error "TypeError"

def heappush : List Value → Eval Value
  | [value, item] => do
      let address ← receiver value
      let values ← items address
      let _ ← Mutable.appendItem address item
      siftDown address 0 values.length
      return .scalar .none
  | _ => Mutable.error "TypeError"

def heappop : List Value → Eval Value
  | [value] => do
      let address ← receiver value
      let last ← Mutable.popItem address (.scalar (.int (-1)))
      let values ← items address
      match values with
      | [] => return last
      | root :: rest =>
          modify fun heap => heap.set address (.list (last :: rest))
          siftUp address 0
          return root
  | _ => Mutable.error "TypeError"

end FormalSW.PyAst.Heapq
