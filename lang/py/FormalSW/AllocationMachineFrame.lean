import lang.py.FormalSW.AllocationFrame
import lang.py.FormalSW.ConstructionMachineFrame

/-! Constructor and named-call entry retain every existing object, including on argument errors. -/
namespace FormalSW.PyAst.HeapCalls.Framing
open Mutable Mutable.Relocation
set_option Elab.async false

inductive AllocationBuiltin : Builtin → Prop
  | list : AllocationBuiltin .list
  | tuple : AllocationBuiltin .tuple
  | bytearray : AllocationBuiltin .bytearray
  | bytes : AllocationBuiltin .bytes
  | set : AllocationBuiltin .set
  | setDisplay : AllocationBuiltin .setDisplay
  | dict : AllocationBuiltin .dict
  | sorted : AllocationBuiltin .sorted
  | sortedReverse : AllocationBuiltin .sortedReverse

theorem step_allocationBuiltin_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (builtin : Builtin) (values : List Value) (stack : List Frame) (globals : Globals)
    (supported : AllocationBuiltin builtin) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.builtin builtin) values, stack, heap⟩ globals) := by
  have stable := SavedCell.allocates address object
  cases supported <;> apply protectGenerator_retains_cell address object stack
  all_goals apply result_retains_cell address object anchors heap _ stack globals saved
  · exact Heapq.preserves_listConstruct _ stable values
  · exact Heapq.preserves_tupleConstruct _ stable values
  · exact Heapq.preserves_bytearray _ stable values
  · exact Heapq.preserves_bytes _ values
  · exact Heapq.preserves_setConstruct _ stable values
  · exact Heapq.preserves_allocateSetValues _ stable values
  · exact Heapq.preserves_dictionaryConstruct _ stable values
  · exact Heapq.preserves_sorted _ stable values
  · exact Heapq.preserves_sortedReverse _ stable values

theorem step_reversedList_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (values : List Value) (stack : List Frame) (globals : Globals)
    (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation .reversedList values, stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object stack _
    (result_retains_cell address object anchors heap _ stack globals saved
      (Heapq.preserves_reversedList _ (SavedCell.allocates address object) values))

theorem invokeMethod_retains_cell (address anchors : Nat) (object : Object) (heap : Heap)
    (receiver : Value) (args : List Arg) (body : List Stmt) (values : List Value)
    (stack : List Frame) (globals : Globals) (saved : SavedCell address object heap) :
    RetainsCell address object (invokeMethod anchors receiver args body values stack heap globals) := by
  unfold invokeMethod
  split <;> exact saved

/-- This proves dispatch and allocation; executing the initializer body needs its own frame proof. -/
theorem construct_retains_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (name : String) (values : List Value) (stack : List Frame) (globals : Globals)
    (saved : SavedCell address object heap) :
    RetainsCell address object (construct module anchors name values stack heap globals) := by
  unfold construct
  cases found : module.findClass name with
  | none => trivial
  | some definition =>
    rcases definition with ⟨origin, body⟩
    dsimp only
    cases initialized : findFunctionIn body "__init__" with
    | none =>
      dsimp only
      cases declared : dataclassFields body with
      | some data =>
        rcases data with ⟨frozen, fields⟩
        exact result_retains_cell address object anchors heap _ stack globals saved
          (Heapq.preserves_allocateDataclass _ (SavedCell.allocates address object) origin name frozen _ values)
      | none =>
        dsimp only
        split
        · exact result_retains_cell address object anchors heap _ stack globals saved
            (Heapq.preserves_allocateInstance _ (SavedCell.allocates address object) origin name)
        · exact saved
    | some initializer =>
      rcases initializer with ⟨args, body⟩
      exact invokeMethod_retains_cell address anchors object _ _ args body values _ globals
        (SavedCell.append address object heap _ saved)

theorem step_namedCall_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (name : String) (values : List Value) (stack : List Frame) (globals : Globals)
    (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.call name) values, stack, heap⟩ globals) := by
  apply protectGenerator_retains_cell address object stack
  change RetainsCell address object (match findFunctionIn module.body name with
    | some (args, body) => match completeArguments args values with
        | some values => .next ⟨.block (executableBody body) (functionEnv args body values globals), stack, heap⟩
        | none => done anchors heap (.error ⟨"TypeError", []⟩) globals
    | none => match libraryFunction module name with
        | some _ => result anchors heap (library module name values) stack globals
        | none => construct module anchors name values stack heap globals)
  split
  · split <;> exact saved
  · split
    · exact result_retains_cell address object anchors heap _ stack globals saved
        (Heapq.preserves_library _ module name values)
    · exact construct_retains_cell module address anchors object heap name values stack globals saved

theorem step_method_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (receiver : Value) (args : List Arg) (body : List Stmt) (values : List Value)
    (stack : List Frame) (globals : Globals) (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.operation (.method receiver args body) values, stack, heap⟩ globals) :=
  protectGenerator_retains_cell address object stack _
    (invokeMethod_retains_cell address anchors object heap receiver args body values stack globals saved)

end FormalSW.PyAst.HeapCalls.Framing
