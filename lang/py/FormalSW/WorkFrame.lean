import lang.py.FormalSW.CursorHeapFrame
import lang.py.FormalSW.ContinuationFrame

/-! Statement and cursor steps retain old objects while preparing the next evaluation. -/
namespace FormalSW.PyAst.HeapCalls.Framing
open Mutable Mutable.Relocation
set_option Elab.async false

theorem step_block_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (body : List Stmt) (env : Env) (stack : List Frame) (globals : Globals)
    (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.block body env, stack, heap⟩ globals) := by
  unfold step
  apply protectGenerator_retains_cell address object stack
  with_reducible repeat' first
    | exact saved
    | trivial
    | apply run_retains_cell _ _ _ _ _ _ _ saved
    | apply run_retains_cell _ _ _ _ _ _ _ retained
    | exact Heapq.preserves_sequence _ _
    | exact Heapq.preserves_reversibleSequence _ _
    | exact Heapq.preserves_dictionaryItemsNext _ _ _ _
    | exact Heapq.preserves_zipItem _ _ _
    | exact Heapq.preserves_allocateTuple _ (SavedCell.allocates address object) _
    | intro result after retained
    | exact retained
    | (solve | simp only [RetainsCell, done, argumentsState_heap] <;> assumption)
    | split
  rename_i _ _ _ _ expressions _ _ _ _
  cases expressions <;> exact saved

theorem step_sortedLoop_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (cursor : SequenceSort) (remaining : List Value) (keys : List (Value × Value))
    (stack : List Frame) (globals : Globals) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.sortedLoop cursor remaining keys, stack, heap⟩ globals) := by
  cases remaining with
  | nil =>
    apply protectGenerator_retains_cell address object stack
    exact result_retains_cell address object anchors heap _ stack globals saved
      (Heapq.preserves_sortedFinish _ (SavedCell.allocates address object) cursor.reverse keys)
  | cons candidate remaining => exact saved

theorem step_extremumLoop_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (cursor : SequenceExtremum) (position : Nat) (best : Option (Value × Value))
    (stack : List Frame) (globals : Globals) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.extremumLoop cursor position best, stack, heap⟩ globals) := by
  apply protectGenerator_retains_cell address object stack
  apply run_retains_cell _ _ _ _ _ _ _ saved (Heapq.preserves_extremumItem _ _ _)
  intro item after retained
  cases item with
  | none => cases best <;> exact retained
  | some candidate => exact retained

theorem step_dictionary_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (entries : List (Expr × Expr)) (values : List (Constant × Value)) (env : Env)
    (stack : List Frame) (globals : Globals) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.dictionary entries values env, stack, heap⟩ globals) := by
  cases entries with
  | nil =>
    exact protectGenerator_retains_cell address object stack _
      (result_retains_cell address object anchors heap _ stack globals saved
        (Heapq.preserves_allocateDict _ (SavedCell.allocates address object) values))
  | cons entry rest => exact saved

theorem step_startRange_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (name : String) (values : List Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Globals) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.startRange name values body otherwise following env, stack, heap⟩ globals) := by
  apply protectGenerator_retains_cell address object stack
  change RetainsCell address object (match rangeBounds values with
    | .ok (start, stop, stride) =>
      .next ⟨.block (.rangeStepLoop name start stop stride body otherwise :: following) env, stack, heap⟩
    | .error error => done anchors heap (.error error) globals)
  split <;> exact saved

end FormalSW.PyAst.HeapCalls.Framing
