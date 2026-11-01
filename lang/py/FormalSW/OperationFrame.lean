import lang.py.FormalSW.CursorHeapFrame
import lang.py.FormalSW.PrimitiveMachineFrame
import lang.py.FormalSW.AllocationMachineFrame

/-! Operation dispatch retains private cells through acquisition, allocation and designated writes. -/
namespace FormalSW.PyAst.HeapCalls.Framing
open Mutable Mutable.Relocation
set_option Elab.async false

/-- Comprehension stores are dispatched before the ordinary primitive evaluator. -/
def operationTargets (operation : Operation) (values : List Value) : List Nat :=
  match operation with
  | .comprehensionStore address => [address]
  | _ => Heapq.primitiveTargets operation values

theorem step_operation_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (operation : Operation) (values : List Value) (stack : List Frame) (globals : Globals)
    (separate : ∀ receiver ∈ operationTargets operation values, receiver ≠ address)
    (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation operation values, stack, heap⟩ globals) := by
  cases operation
  case call name => exact step_namedCall_cell module address anchors object heap name values stack globals saved
  case method receiver args body =>
    exact step_method_cell module address anchors object heap receiver args body values stack globals saved
  case comprehensionStore receiver =>
    have different : receiver ≠ address := separate receiver (by simp [operationTargets])
    clear separate
    apply protectGenerator_retains_cell address object stack
    change RetainsCell address object (match values with
      | [key, value] => result anchors heap (Mutable.setItem (.ref receiver) key value) stack globals
      | _ => .unsupported)
    with_reducible repeat' first
      | trivial
      | apply result_retains_cell _ _ _ _ _ _ _ saved
      | exact setItem_preserves_cell address receiver object _ _ different
      | (solve | simp only [RetainsCell])
      | split
  case builtin builtin =>
    cases builtin <;> first
      | (apply step_primitive_cell _ _ _ _ _ _ _ _ _ (by trivial) _ saved; exact separate)
      | skip
    all_goals simp only [step]
    all_goals apply protectGenerator_retains_cell address object stack
    all_goals simp only [truthSequenceStart]
    all_goals with_reducible repeat' first
      | exact saved
      | apply run_retains_cell _ _ _ _ _ _ _ saved
      | exact Heapq.preserves_sequence _ _
      | intro result after retained
      | exact retained
      | (solve | simp only [RetainsCell, done] <;> assumption)
      | split
  all_goals first
    | (apply step_primitive_cell _ _ _ _ _ _ _ _ _ (by trivial) _ saved; exact separate)
    | skip
  all_goals clear separate
  all_goals simp only [step]
  all_goals apply protectGenerator_retains_cell address object stack
  all_goals try simp only [extremumGeneratorStart, nextGeneratorStart,
    truthGeneratorStart, sumSequenceStart, sumEnter, sumGeneratorStart, comprehensionStart,
    comprehensionTargetsStart, dictionaryValuesCollectionStart, dictionaryValuesStart,
    sumGeneratorTargetsStart, dictionaryItemsSumStart]
  all_goals with_reducible repeat' first
    | exact saved
    | trivial
    | exact SavedCell.append address object _ _ saved
    | exact SavedCell.append address object _ _ retained
    | apply run_retains_cell _ _ _ _ _ _ _ saved
    | apply run_retains_cell _ _ _ _ _ _ _ retained
    | exact Heapq.preserves_sequence _ _
    | exact Heapq.preserves_nextSequence _ _
    | exact Heapq.preserves_sumInitial _ _
    | exact Heapq.preserves_enumerateStart _ _
    | exact Heapq.preserves_permutationRows _ _
    | exact Heapq.preserves_combinationRows _ _
    | exact Heapq.preserves_zipSources _ _
    | intro result after retained
    | exact retained
    | (solve | simp only [RetainsCell, done] <;> first
        | assumption
        | exact SavedCell.append address object _ _ saved
        | exact SavedCell.append address object _ _ retained)
    | contradiction
    | split

end FormalSW.PyAst.HeapCalls.Framing
