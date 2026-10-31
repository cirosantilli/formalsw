import lang.py.FormalSW.SetUpdateRelocation
import lang.py.FormalSW.MachineDictionaryMethods

/-! A captured set-update receiver remains bound throughout argument evaluation and insertion. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_updateSet_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (sources : List Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (addressInside : address < logical.length) (sourcesInside : ∀ source ∈ sources, source.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.updateSet address sources) stack globals)
      (result physicalAnchors physical (Mutable.updateSet (rename address) (sources.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  cases executed : Mutable.updateSet address sources logical with
  | none =>
    have other := (layout.updateSet_unsupported sources address addressInside sourcesInside).mpr executed
    apply Preserves.unchanged layout <;> simp [result, run, executed, other, StepHeap, StepWithin, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    obtain ⟨other, paired, retained, sameLength, bounded⟩ :=
      layout.updateSet sources address addressInside sourcesInside outcome after executed
    exact result_preserves logical physical after other rename rename logicalAnchors physicalAnchors _ _ stack globals outcome
      (fun _ _ => rfl) (Nat.le_of_eq sameLength.symm) (HeapGrows.updateSet _ _ physical _ other paired)
      retained stackInside globalsInside bounded executed paired

end FormalSW.PyAst.HeapCalls.Relocation
