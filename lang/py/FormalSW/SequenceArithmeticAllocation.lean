import lang.py.FormalSW.SequenceAllocation
import lang.py.FormalSW.BufferArithmeticRelocation

/-! Allocating sequence arithmetic keeps shared element references and uses signed repetition counts. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

inductive SequenceArithmeticInput (heap : Mutable.Heap) : BinOp → Value → Value → Bool → List Value → Prop where
  | addLists (left right : Nat) (xs ys : List Value)
      (first : heap[left]? = some (.list xs)) (second : heap[right]? = some (.list ys)) :
      SequenceArithmeticInput heap .add (.ref left) (.ref right) false (xs ++ ys)
  | addTuples (left right : Nat) (xs ys : List Value)
      (first : heap[left]? = some (.tuple xs)) (second : heap[right]? = some (.tuple ys))
      (nonemptyLeft : xs.isEmpty = false) (nonemptyRight : ys.isEmpty = false) :
      SequenceArithmeticInput heap .add (.ref left) (.ref right) true (xs ++ ys)
  | repeatList (address : Nat) (items : List Value) (count : Int)
      (found : heap[address]? = some (.list items)) :
      SequenceArithmeticInput heap .mult (.ref address) (.scalar (.int count)) false (List.replicate count.toNat items).flatten
  | repeatTuple (address : Nat) (items : List Value) (count : Int)
      (found : heap[address]? = some (.tuple items)) (different : count ≠ 1) (nonempty : items.isEmpty = false) :
      SequenceArithmeticInput heap .mult (.ref address) (.scalar (.int count)) true (List.replicate count.toNat items).flatten
  | booleanRight (address : Nat) (flag : Bool) (asTuple : Bool) (items : List Value)
      (input : SequenceArithmeticInput heap .mult (.ref address) (.scalar (.int (if flag then 1 else 0))) asTuple items) :
      SequenceArithmeticInput heap .mult (.ref address) (.scalar (.bool flag)) asTuple items
  | countLeft (address : Nat) (count : Constant) (asTuple : Bool) (items : List Value)
      (input : SequenceArithmeticInput heap .mult (.ref address) (.scalar count) asTuple items) :
      SequenceArithmeticInput heap .mult (.scalar count) (.ref address) asTuple items

theorem SequenceArithmeticInput.within {heap : Mutable.Heap} {op : BinOp} {left right : Value}
    {asTuple : Bool} {items : List Value} (input : SequenceArithmeticInput heap op left right asTuple items)
    (closed : Closed heap) : ∀ value ∈ items, value.edge.Within heap.length := by
  induction input with
  | addLists left right xs ys first second | addTuples left right xs ys first second =>
    intro value member
    rcases List.mem_append.mp member with member | member
    · exact closed _ (List.mem_of_getElem? first) value member
    · exact closed _ (List.mem_of_getElem? second) value member
  | repeatList address items count found | repeatTuple address items count found =>
    exact replicated_values_within _ count.toNat items (closed _ (List.mem_of_getElem? found))
  | booleanRight _ _ _ _ _ ih | countLeft _ _ _ _ _ ih => exact ih

theorem SequenceArithmeticInput.relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    {op : BinOp} {left right : Value} {asTuple : Bool} {items : List Value}
    (input : SequenceArithmeticInput logical op left right asTuple items) (layout : ExecutionLayout logical physical rename) :
    SequenceArithmeticInput physical op (relocateValue rename left) (relocateValue rename right) asTuple
      (items.map (relocateValue rename)) := by
  induction input with
  | addLists left right xs ys first second =>
    simpa only [List.map_append] using SequenceArithmeticInput.addLists (rename left) (rename right)
      (xs.map (relocateValue rename)) (ys.map (relocateValue rename)) (layout.runtime.lookup _ _ first) (layout.runtime.lookup _ _ second)
  | addTuples left right xs ys first second nonemptyLeft nonemptyRight =>
    simpa only [List.map_append] using SequenceArithmeticInput.addTuples (rename left) (rename right)
      (xs.map (relocateValue rename)) (ys.map (relocateValue rename)) (layout.runtime.lookup _ _ first) (layout.runtime.lookup _ _ second)
      (by simpa only [List.isEmpty_map] using nonemptyLeft) (by simpa only [List.isEmpty_map] using nonemptyRight)
  | repeatList address items count found =>
    simpa only [map_replicated_values] using SequenceArithmeticInput.repeatList (rename address)
      (items.map (relocateValue rename)) count (layout.runtime.lookup _ _ found)
  | repeatTuple address items count found different nonempty =>
    simpa only [map_replicated_values] using SequenceArithmeticInput.repeatTuple (rename address)
      (items.map (relocateValue rename)) count (layout.runtime.lookup _ _ found) different
      (by simpa only [List.isEmpty_map] using nonempty)
  | booleanRight address flag asTuple items input ih => exact .booleanRight (rename address) flag asTuple _ ih
  | countLeft address count asTuple items input ih => exact .countLeft (rename address) count asTuple _ ih

theorem SequenceArithmeticInput.binary {heap : Mutable.Heap} {op : BinOp} {left right : Value}
    {asTuple : Bool} {items : List Value} (input : SequenceArithmeticInput heap op left right asTuple items) :
    Mutable.binary op left right heap = allocateSequence asTuple items heap := by
  induction input with
  | addLists left right xs ys first second => exact binary_add_lists_eval heap left right xs ys first second
  | addTuples left right xs ys first second nonemptyLeft nonemptyRight =>
    simpa only [nonemptyLeft, nonemptyRight, Bool.false_eq_true, if_false] using binary_add_tuples_eval heap left right xs ys first second
  | repeatList address items count found => exact binary_mult_list_eval heap address items count found
  | repeatTuple address items count found different nonempty =>
    simpa only [different, nonempty, Bool.false_eq_true, or_self, if_false] using binary_mult_tuple_eval heap address items count found
  | booleanRight address flag asTuple items input ih =>
    have same : Mutable.binary .mult (.ref address) (.scalar (.bool flag)) heap =
        Mutable.binary .mult (.ref address) (.scalar (.int (if flag then 1 else 0))) heap := by cases flag <;> rfl
    exact same.trans ih
  | countLeft address count asTuple items input ih => exact (binary_mult_ref_value_comm heap address (.scalar count)).trans ih

end FormalSW.PyAst.HeapCalls.Relocation
