import lang.py.FormalSW.MachineFrame
import lang.py.FormalSW.ConstructionFrame

/-! Constructor steps retain existing cells while filling fresh sets and dictionaries. -/
namespace FormalSW.PyAst.HeapCalls.Framing
open Mutable Mutable.Relocation
set_option Elab.async false

theorem step_setDisplay_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (values : List Value) (stack : List Frame) (globals : Globals)
    (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.builtin .setDisplay) values, stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved
      (Heapq.preserves_allocateSetValues _ (SavedCell.allocates address object) values))

theorem step_setConstruct_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (values : List Value) (stack : List Frame) (globals : Globals)
    (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.builtin .set) values, stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved
      (Heapq.preserves_setConstruct _ (SavedCell.allocates address object) values))

theorem step_dictionaryConstruct_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (values : List Value) (stack : List Frame) (globals : Globals)
    (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.builtin .dict) values, stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved
      (Heapq.preserves_dictionaryConstruct _ (SavedCell.allocates address object) values))

end FormalSW.PyAst.HeapCalls.Framing
