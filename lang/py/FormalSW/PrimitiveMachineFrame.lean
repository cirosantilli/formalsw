import lang.py.FormalSW.PrimitiveHeapFrame
import lang.py.FormalSW.MachineFrame

/-! Unified private-cell preservation for primitive interpreter dispatch. -/
namespace FormalSW.PyAst.HeapCalls.Framing
open Mutable Mutable.Relocation
set_option Elab.async false

/-- Calls and iterator acquisition have separate transitions before their bodies execute. -/
def PrimitiveDispatch : Operation → Prop
  | .call _ | .method _ _ _ | .builtin .all | .builtin .any
    | .extremumGenerator _ _ _ _ _ | .nextGenerator _ _ _ _ | .truthGenerator _ _ _ _
    | .sumSequence | .sumGenerator _ _ _ _ | .comprehension _ _ _
    | .combinationStart _ _ _ _ _ | .permutationStart _ _ _ _ _ | .zipStart _ _ _ _ _
    | .comprehensionTargets _ _ _ | .generatorCollect _ _ _ _ | .setComprehension _ _ _
    | .dictionaryComprehension _ _ _ _ | .comprehensionStore _ | .sumGeneratorTargets _ _ _ _ => False
  | _ => True

theorem primitive_dispatch (module : Module) (anchors : Nat) (heap : Heap) (operation : Operation)
    (values : List Value) (stack : List Frame) (globals : Globals) (direct : PrimitiveDispatch operation) :
    step module anchors ⟨.operation operation values, stack, heap⟩ globals =
      protectGenerator stack (result anchors heap (primitive operation values) stack globals) := by
  cases operation <;> first | rfl | exact False.elim direct | skip
  case builtin builtin => cases builtin <;> first | rfl | exact False.elim direct

theorem primitive_preserves_cell (address : Nat) (object : Object) (operation : Operation) (values : List Value)
    (separate : ∀ receiver ∈ Heapq.primitiveTargets operation values, receiver ≠ address) :
    Heapq.Preserves (SavedCell address object) (primitive operation values) :=
  Heapq.preserves_primitive _ (SavedCell.allocates address object) operation values
    (fun receiver member => SavedCell.update address receiver object (separate receiver member))

theorem step_primitive_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (operation : Operation) (values : List Value) (stack : List Frame) (globals : Globals)
    (direct : PrimitiveDispatch operation)
    (separate : ∀ receiver ∈ Heapq.primitiveTargets operation values, receiver ≠ address)
    (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation operation values, stack, heap⟩ globals) := by
  rw [primitive_dispatch module anchors heap operation values stack globals direct]
  exact protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved
      (primitive_preserves_cell address object operation values separate))

theorem step_unary_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (op : UnaryOp) (value : Value) (stack : List Frame) (globals : Globals)
    (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.value value, .unary op :: stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object (.unary op :: stack) _
    (result_retains_cell address object anchors heap _ stack globals saved (Heapq.preserves_unary _ op value))

theorem step_compare_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (op : CmpOp) (left right : Value) (stack : List Frame) (globals : Globals)
    (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.value right, .compareRight op left :: stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object (.compareRight op left :: stack) _
    (result_retains_cell address object anchors heap _ stack globals saved (Heapq.preserves_compare _ op left right))

end FormalSW.PyAst.HeapCalls.Framing
