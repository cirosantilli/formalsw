import lang.py.FormalSW.SetOperationsRelocation
import lang.py.FormalSW.ConstructionIsolation

/-! Scalar-set union and difference allocate fresh results even when their operands alias. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

inductive SetArithmeticInput (heap : Mutable.Heap) : BinOp → Value → Value → List Constant → Prop where
  | union (left right : Nat) (xs ys : List Constant)
      (first : heap[left]? = some (.set xs)) (second : heap[right]? = some (.set ys)) :
      SetArithmeticInput heap .bitOr (.ref left) (.ref right) (ScalarSet.union xs ys)
  | difference (left right : Nat) (xs ys : List Constant)
      (first : heap[left]? = some (.set xs)) (second : heap[right]? = some (.set ys)) :
      SetArithmeticInput heap .sub (.ref left) (.ref right) (ScalarSet.difference xs ys)

theorem SetArithmeticInput.relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    {op : BinOp} {left right : Value} {items : List Constant}
    (input : SetArithmeticInput logical op left right items) (layout : ExecutionLayout logical physical rename) :
    SetArithmeticInput physical op (relocateValue rename left) (relocateValue rename right) items := by
  cases input with
  | union left right xs ys first second =>
    exact .union (rename left) (rename right) xs ys (layout.runtime.lookup _ _ first) (layout.runtime.lookup _ _ second)
  | difference left right xs ys first second =>
    exact .difference (rename left) (rename right) xs ys (layout.runtime.lookup _ _ first) (layout.runtime.lookup _ _ second)

theorem SetArithmeticInput.binary {heap : Mutable.Heap} {op : BinOp} {left right : Value} {items : List Constant}
    (input : SetArithmeticInput heap op left right items) :
    Mutable.binary op left right heap = some (.ok (.ref heap.length), heap ++ [.set items]) := by
  cases input with
  | union left right xs ys first second => exact Mutable.binary_union_sets heap left right xs ys first second
  | difference left right xs ys first second => exact Mutable.binary_difference_sets heap left right xs ys first second

end FormalSW.PyAst.HeapCalls.Relocation
