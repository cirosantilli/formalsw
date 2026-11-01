import lang.py.FormalSW.MachineFrame
import lang.py.FormalSW.BinaryHeapFrame

/-! Compound mutations preserve private cells in ordinary and augmented interpreter steps. -/
namespace FormalSW.PyAst.HeapCalls.Framing
open Mutable Mutable.Relocation
set_option Elab.async false

theorem step_setSlice_cell (module : Module) (address receiver anchors : Nat) (object : Object)
    (heap : Heap) (lower upper stride replacement : Value) (stack : List Frame) (globals : Globals)
    (separate : receiver ≠ address) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors
      ⟨.operation (.setSlice replacement) [.ref receiver, lower, upper, stride], stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved
      (Heapq.preserves_setSlice receiver _ (SavedCell.update address receiver object separate) lower upper stride replacement))

theorem step_dictionaryClear_cell (module : Module) (address receiver anchors : Nat) (object : Object)
    (heap : Heap) (stack : List Frame) (globals : Globals)
    (separate : receiver ≠ address) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.dictionaryClear receiver) [], stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved
      (Heapq.preserves_clearDictionary receiver _ (SavedCell.update address receiver object separate)))

theorem step_sort_cell (module : Module) (address receiver anchors : Nat) (object : Object)
    (heap : Heap) (stack : List Frame) (globals : Globals)
    (separate : receiver ≠ address) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.sort receiver) [], stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved
      (Heapq.preserves_sort receiver _ (SavedCell.update address receiver object separate)))

theorem step_sortReverse_cell (module : Module) (address receiver anchors : Nat) (object : Object)
    (heap : Heap) (reverse : Value) (stack : List Frame) (globals : Globals)
    (separate : receiver ≠ address) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.sortReverse receiver) [reverse], stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved
      (Heapq.preserves_sortReverse receiver _ (SavedCell.update address receiver object separate) reverse))

/-- Every binary operator, including its augmented form, retains an unrelated existing cell. -/
theorem step_binary_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (op : BinOp) (left right : Value) (inPlace : Bool) (stack : List Frame) (globals : Globals)
    (separate : inPlace = true → left ≠ .ref address) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.value right, .binaryRight op left inPlace :: stack, heap⟩ globals) := by
  apply protectGenerator_retains_cell address object (.binaryRight op left inPlace :: stack)
  apply result_retains_cell address object anchors heap _ stack globals saved
  cases inPlace with
  | false => exact Heapq.preserves_binary _ (SavedCell.allocates address object) op left right
  | true =>
    apply Heapq.preserves_inplace _ (SavedCell.allocates address object) op left right
    intro receiver same
    exact SavedCell.update address receiver object (fun equal => separate rfl (same.trans (congrArg Value.ref equal)))

end FormalSW.PyAst.HeapCalls.Framing
