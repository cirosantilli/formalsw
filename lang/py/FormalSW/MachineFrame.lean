import lang.py.FormalSW.HeapFrame

/-! Lift heap-cell preservation into actual interpreter steps, including generator errors. -/
namespace FormalSW.PyAst.HeapCalls.Framing
open Mutable Mutable.Relocation
set_option Elab.async false

def RetainsCell (address : Nat) (object : Object) : Step State Completion → Prop
  | .next state => SavedCell address object state.heap
  | .done (.ok completion) => SavedCell address object completion.heap
  | .done (.error _) | .unsupported => True

theorem protectGenerator_retains_cell (address : Nat) (object : Object) (stack : List Frame)
    (transition : Step State Completion) (retained : RetainsCell address object transition) :
    RetainsCell address object (protectGenerator stack transition) := by
  cases transition with
  | next | unsupported => exact retained
  | done outcome =>
    cases outcome with
    | error => trivial
    | ok completion =>
      rcases completion with ⟨outcome, globals, heap, anchors⟩
      cases outcome <;> exact retained

theorem result_retains_cell (address : Nat) (object : Object) (anchors : Nat) (heap : Heap)
    (action : Eval Value) (stack : List Frame) (globals : Globals)
    (saved : SavedCell address object heap) (preserved : Heapq.Preserves (SavedCell address object) action) :
    RetainsCell address object (result anchors heap action stack globals) := by
  cases executed : action heap with
  | none => simp only [result, run, executed, RetainsCell]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have retained := preserved heap outcome after saved executed
    cases outcome <;> simpa only [result, run, executed, done, RetainsCell] using retained

theorem step_append_cell (module : Module) (address receiver anchors : Nat) (object : Object)
    (heap : Heap) (value : Value) (stack : List Frame) (globals : Globals)
    (separate : receiver ≠ address) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.append receiver) [value], stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved
      (appendItem_preserves_cell address receiver object value separate))

theorem step_setItem_cell (module : Module) (address receiver anchors : Nat) (object : Object)
    (heap : Heap) (index value : Value) (stack : List Frame) (globals : Globals)
    (separate : receiver ≠ address) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.setItem value) [.ref receiver, index], stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved
      (setItem_preserves_cell address receiver object index value separate))

theorem step_pop_cell (module : Module) (address receiver anchors : Nat) (object : Object)
    (heap : Heap) (index : Value) (stack : List Frame) (globals : Globals)
    (separate : receiver ≠ address) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.pop receiver) [index], stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved
      (popItem_preserves_cell address receiver object index separate))

theorem step_field_cell (module : Module) (address receiver anchors : Nat) (object : Object)
    (heap : Heap) (name : String) (value : Value) (stack : List Frame) (globals : Globals)
    (separate : receiver ≠ address) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.setField name value) [.ref receiver], stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved
      (writeField_preserves_cell address receiver object name value separate))

theorem step_add_cell (module : Module) (address receiver anchors : Nat) (object : Object)
    (heap : Heap) (value : Value) (stack : List Frame) (globals : Globals)
    (separate : receiver ≠ address) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.add receiver) [value], stack, heap⟩ globals) := by
  have stable := SavedCell.update address receiver object separate
  exact protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved (Heapq.preserves_addItem receiver _ stable value))

theorem step_setDefault_cell (module : Module) (address receiver anchors : Nat) (object : Object)
    (heap : Heap) (key value : Value) (stack : List Frame) (globals : Globals)
    (separate : receiver ≠ address) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.dictionarySetDefault receiver) [key, value], stack, heap⟩ globals) := by
  have stable := SavedCell.update address receiver object separate
  exact protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved (Heapq.preserves_dictionarySetDefault receiver _ stable key value))

theorem step_heapify_cell (module : Module) (address receiver anchors : Nat) (object : Object)
    (heap : Heap) (stack : List Frame) (globals : Globals)
    (separate : receiver ≠ address) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.builtin .heapqHeapify) [.ref receiver], stack, heap⟩ globals) := by
  have stable := SavedCell.update address receiver object separate
  exact protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved (Heapq.preserves_heapify receiver _ (stable.swaps receiver _)))

theorem step_heappush_cell (module : Module) (address receiver anchors : Nat) (object : Object)
    (heap : Heap) (value : Value) (stack : List Frame) (globals : Globals)
    (separate : receiver ≠ address) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.builtin .heapqPush) [.ref receiver, value], stack, heap⟩ globals) := by
  have stable := SavedCell.update address receiver object separate
  exact protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved (Heapq.preserves_heappush receiver _ stable value))

theorem step_heappop_cell (module : Module) (address receiver anchors : Nat) (object : Object)
    (heap : Heap) (stack : List Frame) (globals : Globals)
    (separate : receiver ≠ address) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.builtin .heapqPop) [.ref receiver], stack, heap⟩ globals) := by
  have stable := SavedCell.update address receiver object separate
  exact protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved (Heapq.preserves_heappop receiver _ stable))

theorem step_list_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (values : List Value) (stack : List Frame) (globals : Globals)
    (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation .list values, stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved
      (Heapq.preserves_allocate _ (SavedCell.allocates address object) values))

theorem step_tuple_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (values : List Value) (stack : List Frame) (globals : Globals)
    (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation .tuple values, stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved
      (Heapq.preserves_allocateTuple _ (SavedCell.allocates address object) values))

end FormalSW.PyAst.HeapCalls.Framing
