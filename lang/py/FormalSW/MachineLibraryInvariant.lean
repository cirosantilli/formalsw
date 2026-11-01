import lang.py.FormalSW.MachineExpressionInvariant

/-! Modeled library calls use scalar arguments and retain all prior heap effects. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

def libraryScalars : List Value → Except ExceptionObject (List Constant)
  | [] => .ok []
  | .scalar scalar :: rest => (libraryScalars rest).map (List.cons scalar)
  | .ref _ :: _ => .error ⟨"TypeError", []⟩

theorem libraryScalars_relocates (values : List Value) (rename : Nat → Nat) :
    libraryScalars (values.map (relocateValue rename)) = libraryScalars values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    cases value <;> simp [libraryScalars, relocateValue, ih]

theorem library_arguments (extract : Value → Mutable.Eval Constant)
    (scalar : ∀ value, extract (.scalar value) = pure value)
    (reference : ∀ address, extract (.ref address) = Mutable.error "TypeError")
    (values : List Value) (heap : Mutable.Heap) :
    values.mapM extract heap = some (libraryScalars values, heap) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    cases value with
    | ref address => rw [List.mapM_cons, reference]; rfl
    | scalar value =>
      rw [List.mapM_cons, scalar]
      simp [Mutable.eval_bind, ih]
      rfl

/-- This normalizes argument validation without evaluating the mathematical library function. -/
theorem library_scalarResult (module : Module) (name : String) (values : List Value) :
    library module name values = scalarResult
      ((libraryFunction module name).map fun function => (libraryScalars values).bind function) := by
  funext heap
  cases found : libraryFunction module name with
  | none => simp [library, found, scalarResult, Mutable.unsupported]
  | some function =>
    simp only [library, found, Mutable.eval_bind, Option.map_some]
    rw [library_arguments _ (fun _ => rfl) (fun _ => rfl)]
    cases collected : libraryScalars values with
    | error exception => rfl
    | ok scalars => rfl

theorem result_library_preserves (module : Module) (name : String)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (library module name values) stack globals)
      (result physicalAnchors physical (library module name (values.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  simp only [library_scalarResult, libraryScalars_relocates]
  exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors _ stack globals
    layout stackInside globalsInside

end FormalSW.PyAst.HeapCalls.Relocation
