import lang.py.FormalSW.StringMethodRelocation
import lang.py.FormalSW.MachineSequenceConstruction

/-! String methods retain argument effects, allocation order and unsupported protocol cases. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_join_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (separator : String) (source : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (sourceInside : source.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (primitive (.join separator) [source]) stack globals)
      (result physicalAnchors physical (primitive (.join separator) [relocateValue rename source])
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  rw [primitive_join_pool, primitive_join_pool, result_bind, result_bind]
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ (List.map (relocateValue rename)) _ _ globals layout globalsInside
    (fun outcome after executed => positionalPool_keeps_heap logical source outcome after executed)
    (positionalPool_relocates layout.runtime source sourceInside)
  intro items _
  rw [joinValues_scalar, joinValues_scalar, stringValues_relocates]
  exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors _ stack globals layout stackInside globalsInside

theorem result_stringIndexFailure_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (inside : address < logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (stringIndexFailure address) stack globals)
      (result physicalAnchors physical (stringIndexFailure (rename address))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
  have moved := layout.runtime.lookup address _ found
  cases object : logical[address] <;> simp only [object, relocateObject] at moved
  case «instance» origin name fields | dataInstance origin name frozen declared fields =>
    apply Preserves.unchanged layout <;>
      simp [result, run, stringIndexFailure, found, object, moved, Mutable.unsupported, StepHeap, StepWithin, relocateStep]
  all_goals
    simpa [result, run, stringIndexFailure, found, object, moved, scalarResult, Mutable.error] using
      result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout stackInside globalsInside

theorem result_replace_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (text : String) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (primitive (.replace text) values) stack globals)
      (result physicalAnchors physical (primitive (.replace text) (values.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have failed := result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
    (some (.error ⟨"TypeError", []⟩)) stack globals layout stackInside globalsInside
  rcases values with _ | ⟨old, _ | ⟨new, _ | ⟨count, _ | ⟨extra, rest⟩⟩⟩⟩
  case cons.cons.nil =>
    cases old <;> cases new
    case scalar.scalar old new =>
      exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (Strings.replaceCall text [old, new])) stack globals layout stackInside globalsInside
    all_goals exact failed
  case cons.cons.cons.nil =>
    cases old <;> cases new <;> cases count
    case scalar.scalar.scalar old new count =>
      exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (Strings.replaceCall text [old, new, count])) stack globals layout stackInside globalsInside
    case scalar.scalar.ref old new address =>
      have inside := valuesInside (.ref address) (by simp)
      cases old <;> cases new
      case string.string old new =>
        have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
        have moved := layout.runtime.lookup address _ found
        simpa only [result, run, List.map_cons, List.map_nil, relocateValue,
          primitive_replace_ref logical text old new address _ found,
          primitive_replace_ref physical text old new (rename address) _ moved] using
          result_stringIndexFailure_preserves logical physical rename logicalAnchors physicalAnchors address stack globals layout inside stackInside globalsInside
      all_goals exact failed
    all_goals exact failed
  case cons.nil => cases old <;> exact failed
  case cons.cons.cons.cons => cases old <;> cases new <;> cases count <;> exact failed
  all_goals exact failed

theorem result_zfill_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (text : String) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (primitive (.zfill text) values) stack globals)
      (result physicalAnchors physical (primitive (.zfill text) (values.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  rcases values with _ | ⟨width, _ | ⟨extra, rest⟩⟩
  case cons.nil =>
    cases width with
    | scalar scalar =>
      exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (Strings.zfillCall text [scalar])) stack globals layout stackInside globalsInside
    | ref address =>
      exact result_stringIndexFailure_preserves logical physical rename logicalAnchors physicalAnchors address stack globals layout
        (valuesInside (.ref address) (by simp)) stackInside globalsInside
  case cons.cons =>
    cases width <;>
      exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout stackInside globalsInside
  all_goals
    exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
      (some (.error ⟨"TypeError", []⟩)) stack globals layout stackInside globalsInside

inductive StringMethodOperation : Operation → Prop
  | strip (text : String) : StringMethodOperation (.strip text)
  | split (text : String) : StringMethodOperation (.splitWhitespace text)
  | replace (text : String) : StringMethodOperation (.replace text)
  | zfill (text : String) : StringMethodOperation (.zfill text)
  | upper (text : String) : StringMethodOperation (.upper text)
  | join (separator : String) : StringMethodOperation (.join separator)

theorem step_stringMethod_preserves (module : Module)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (operation : Operation) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (covered : StringMethodOperation operation)
    (inside : StateWithin ⟨.operation operation values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation operation values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation operation values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases covered with
  | strip text =>
    cases values with
    | nil =>
      exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.ok (.string (Strings.stripWhitespace text)))) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2
    | cons value rest => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  | split text =>
    cases values with
    | nil =>
      have bounded : ∀ value ∈ (Strings.splitWhitespace text).map (fun word => Mutable.Value.scalar (.string word)), value.edge.Within logical.length := by
        intro value member
        obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
        trivial
      have allocated := result_allocateList_preserves logical physical rename logicalAnchors physicalAnchors
        ((Strings.splitWhitespace text).map fun word => .scalar (.string word)) stack globals layout bounded inside.2 globalsInside
      simpa only [List.map_map, Function.comp_def, relocateValue] using allocated.protectGenerator stack inside.2
    | cons value rest => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  | replace text =>
    exact (result_replace_preserves logical physical rename logicalAnchors physicalAnchors text values stack globals
      layout inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2
  | zfill text =>
    exact (result_zfill_preserves logical physical rename logicalAnchors physicalAnchors text values stack globals
      layout inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2
  | upper text =>
    cases values with
    | nil =>
      exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (Strings.upperCall text []) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2
    | cons value rest =>
      exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2
  | join separator =>
    rcases values with _ | ⟨source, _ | ⟨extra, rest⟩⟩
    case cons.nil =>
      exact (result_join_preserves logical physical rename logicalAnchors physicalAnchors separator source stack globals
        layout (inside.1.2 source (by simp)) inside.2 globalsInside).protectGenerator stack inside.2
    all_goals
      exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_stringMethod_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (operation : Operation) (values : List Mutable.Value) (stack : List Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (covered : StringMethodOperation operation)
    (inside : StateWithin logical.length (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_stringMethod_preserves module logical physical rename logicalAnchors physicalAnchors
      operation values stack globals layout covered ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
