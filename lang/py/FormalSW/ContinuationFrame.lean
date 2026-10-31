import lang.py.FormalSW.AcquisitionHeapFrame
import lang.py.FormalSW.PrimitiveMachineFrame
import lang.py.FormalSW.CompositeMachineFrame

/-! A value continuation can write only its immediate assignment or augmented receiver. -/
namespace FormalSW.PyAst.HeapCalls.Framing
open Mutable Mutable.Relocation
set_option Elab.async false

/-- Saved consumers may mention protected cells; only the frame being resumed can write. -/
def FrameSeparate (address : Nat) : Frame → Prop
  | .writeAttribute receiver _ _ _ | .writeItem receiver _ _ _ => receiver ≠ .ref address
  | .binaryRight _ left inPlace => inPlace = true → left ≠ .ref address
  | _ => True

theorem argumentsState_heap (operation : Operation) (env : Env) (values : List Value)
    (expressions : List Expr) (stack : List Frame) (heap : Heap) :
    (argumentsState operation env values expressions stack heap).heap = heap := by
  cases expressions <;> rfl

theorem expandedArgumentsState_heap (operation : Operation) (env : Env) (values : List Value)
    (expressions : List Expr) (stack : List Frame) (heap : Heap) :
    (expandedArgumentsState operation env values expressions stack heap).heap = heap := by
  unfold expandedArgumentsState
  split
  · rfl
  · split <;> rfl

theorem step_value_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (value : Value) (stack : List Frame) (globals : Globals)
    (separate : ∀ frame ∈ stack.head?, FrameSeparate address frame)
    (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.value value, stack, heap⟩ globals) := by
  cases stack with
  | nil => exact saved
  | cons frame stack =>
    have separated : FrameSeparate address frame := separate frame rfl
    cases frame
    case binaryRight op left inPlace =>
      exact step_binary_cell module address anchors object heap op left value inPlace stack globals separated saved
    case writeAttribute receiver name rest env =>
      apply protectGenerator_retains_cell
      apply result_retains_cell _ _ _ _ _ _ _ saved
      cases receiver with
      | scalar scalar => exact Heapq.preserves_writeField_scalar _ scalar name value
      | ref receiver =>
        exact writeField_preserves_cell address receiver object name value
          (fun same => separated (congrArg Value.ref same))
    case writeItem receiver index rest env =>
      apply protectGenerator_retains_cell
      apply result_retains_cell _ _ _ _ _ _ _ saved
      cases receiver with
      | scalar scalar => exact Heapq.Preserves.error _ "TypeError"
      | ref receiver =>
        exact setItem_preserves_cell address receiver object index value
          (fun same => separated (congrArg Value.ref same))
    case arguments operation done rest env =>
      cases rest <;> exact saved
    case rangeArguments name done rest body otherwise following env =>
      cases rest <;> exact saved
    all_goals first | exact saved | apply protectGenerator_retains_cell address object _ _
    all_goals simp only [sumEnter, dictionaryItemsStart, dictionaryValuesStart]
    all_goals with_reducible repeat' first
      | exact saved
      | trivial
      | apply result_retains_cell _ _ _ _ _ _ _ saved
      | exact Heapq.preserves_getAttribute _ _ _ _
      | exact Heapq.preserves_compare _ _ _ _
      | exact Heapq.preserves_unary _ _ _
      | apply run_retains_cell _ _ _ _ _ _ _ saved
      | apply run_retains_cell _ _ _ _ _ _ _ retained
      | exact Heapq.preserves_bindMethod _ _ _ _
      | exact Heapq.preserves_sumInitial _ _
      | exact Heapq.preserves_truth _ _
      | exact Heapq.preserves_starItems _ _
      | exact Heapq.preserves_addReceiver _ _
      | exact Heapq.preserves_appendReceiver _ _
      | exact Heapq.preserves_getItem _ _ _
      | exact Heapq.preserves_sortedStart _ _ _
      | exact Heapq.preserves_sequence _ _
      | exact Heapq.preserves_extremumChoose _ _ _ _ _
      | exact Heapq.preserves_reversibleSequence _ _
      | exact Heapq.preserves_enumerateStart _ _
      | intro result after retained
      | exact retained
      | (solve | simp only [RetainsCell, done, argumentsState_heap, expandedArgumentsState_heap, generatorArguments] <;> assumption)
      | split

end FormalSW.PyAst.HeapCalls.Framing
