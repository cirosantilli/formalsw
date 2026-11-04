import lang.py.FormalSW.DictionaryMethodRelocation
import lang.py.FormalSW.MachineItemInvariant
import lang.py.FormalSW.MachineRunInvariant

/-! Dictionary methods preserve argument effects, stored aliases and mutation outcomes. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_bind {α : Type} (anchors : Nat) (heap : Mutable.Heap)
    (action : Mutable.Eval α) (next : α → Mutable.Eval Value) (stack : List Frame) (globals : Mutable.Globals) :
    result anchors heap (action >>= next) stack globals =
      run anchors heap action (fun value after => result anchors after (next value) stack globals) globals := by
  cases executed : action heap with
  | none => simp [result, run, Mutable.eval_bind, executed]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    cases outcome <;> simp [result, run, Mutable.eval_bind, executed]

theorem result_pure_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (valueInside : value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (pure value) stack globals)
      (result physicalAnchors physical (pure (relocateValue rename value))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) :=
  Preserves.unchanged layout rfl ⟨valueInside, stackInside⟩ rfl

/-- The default is returned only after the indexed write succeeds. -/
theorem result_setItem_return_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver key value : Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (receiverInside : receiver.edge.Within logical.length) (keyInside : key.edge.Within logical.length)
    (valueInside : value.edge.Within logical.length) (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (do let _ ← Mutable.setItem receiver key value; pure value) stack globals)
      (result physicalAnchors physical
        (do let _ ← Mutable.setItem (relocateValue rename receiver) (relocateValue rename key) (relocateValue rename value)
            pure (relocateValue rename value)) (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  cases written : Mutable.setItem receiver key value logical with
  | none =>
    have other := (layout.runtime.setItem_unsupported layout.closed receiver key value receiverInside keyInside).mpr written
    apply Preserves.unchanged layout <;>
      simp [result, run, Mutable.eval_bind, written, other, StepHeap, StepWithin, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    obtain ⟨other, paired, retained⟩ := layout.setItem receiver key value receiverInside keyInside valueInside outcome after written
    have logicalSize := (setItem_effect logical after receiver key value outcome written).1
    have physicalSize := (setItem_effect physical other (relocateValue rename receiver) (relocateValue rename key)
      (relocateValue rename value) _ paired).1
    apply result_preserves logical physical after other rename rename logicalAnchors physicalAnchors _ _ stack globals
      (outcome.map (fun _ => value)) (fun _ _ => rfl) (Nat.le_of_eq logicalSize.symm)
      (Nat.le_of_eq physicalSize.symm) retained stackInside globalsInside
    · intro returned success
      cases outcome with
      | error exception => cases success
      | ok ignored =>
        have same : value = returned := Except.ok.inj success
        rw [← same, logicalSize]
        exact valueInside
    · cases outcome <;> simp [Mutable.eval_bind, written, Except.map]
    · cases outcome <;> simp [Mutable.eval_bind, paired, Except.map]

theorem result_dictionaryGet_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (key fallback : Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (addressInside : address < logical.length) (keyInside : key.edge.Within logical.length)
    (fallbackInside : fallback.edge.Within logical.length) (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.dictionaryGet address key fallback) stack globals)
      (result physicalAnchors physical (Mutable.dictionaryGet (rename address) (relocateValue rename key) (relocateValue rename fallback))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have normalized (address : Nat) (key fallback : Value) : Mutable.dictionaryGet address key fallback =
      (do let previous ← dictionaryLookup address key; pure (previous.getD fallback)) :=
    funext (fun heap => dictionaryGet_lookup heap address key fallback)
  rw [normalized, normalized, result_bind, result_bind]
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _
    (Option.map (relocateValue rename)) _ _ globals layout globalsInside
    (fun outcome after executed => (dictionaryLookup_effect logical after layout.closed address key outcome executed).1)
    (layout.runtime.dictionaryLookup_relocates layout.closed address key addressInside keyInside)
  intro previous read
  have bounded := (dictionaryLookup_effect logical logical layout.closed address key (.ok previous) read).2
  cases previous with
  | none => exact result_pure_preserves logical physical rename logicalAnchors physicalAnchors fallback stack globals layout fallbackInside stackInside
  | some value => exact result_pure_preserves logical physical rename logicalAnchors physicalAnchors value stack globals layout (bounded value rfl) stackInside

theorem result_dictionarySetDefault_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (key fallback : Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (addressInside : address < logical.length) (keyInside : key.edge.Within logical.length)
    (fallbackInside : fallback.edge.Within logical.length) (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.dictionarySetDefault address key fallback) stack globals)
      (result physicalAnchors physical (Mutable.dictionarySetDefault (rename address) (relocateValue rename key) (relocateValue rename fallback))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have normalized (address : Nat) (key fallback : Value) : Mutable.dictionarySetDefault address key fallback =
      (do let previous ← dictionaryLookup address key
          match previous with
          | some value => pure value
          | none => let _ ← Mutable.setItem (.ref address) key fallback; pure fallback) :=
    funext (fun heap => dictionarySetDefault_lookup heap address key fallback)
  rw [normalized, normalized, result_bind, result_bind]
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _
    (Option.map (relocateValue rename)) _ _ globals layout globalsInside
    (fun outcome after executed => (dictionaryLookup_effect logical after layout.closed address key outcome executed).1)
    (layout.runtime.dictionaryLookup_relocates layout.closed address key addressInside keyInside)
  intro previous read
  have bounded := (dictionaryLookup_effect logical logical layout.closed address key (.ok previous) read).2
  cases previous with
  | none =>
    exact result_setItem_return_preserves logical physical rename logicalAnchors physicalAnchors
      (.ref address) key fallback stack globals layout addressInside keyInside fallbackInside stackInside globalsInside
  | some value => exact result_pure_preserves logical physical rename logicalAnchors physicalAnchors value stack globals layout (bounded value rfl) stackInside

theorem result_clearDictionary_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (addressInside : address < logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (clearDictionary address) stack globals)
      (result physicalAnchors physical (clearDictionary (rename address))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem addressInside
  have moved := layout.runtime.lookup address _ found
  cases object : logical[address] <;> simp only [object, relocateObject] at moved
  case dict entries =>
    have retained := layout.set_nonempty address _ (.dict []) (found.trans (congrArg some object))
      (by simp) (by simp) (by simp [ObjectWithin, objectValues])
    apply result_preserves logical physical _ _ rename rename logicalAnchors physicalAnchors _ _ stack globals
      (.ok (.scalar .none)) (fun _ _ => rfl) (by simp) (by simp) retained stackInside globalsInside
    · intro value same; cases same; trivial
    · simp [clearDictionary, found, object, Except.map]
    · simp [clearDictionary, moved, Except.map, relocateValue, relocateObject]
  case keyDict entries =>
    have retained := layout.set_nonempty address _ (.keyDict []) (found.trans (congrArg some object))
      (by simp) (by simp) (by simp [ObjectWithin, objectValues])
    apply result_preserves logical physical _ _ rename rename logicalAnchors physicalAnchors _ _ stack globals
      (.ok (.scalar .none)) (fun _ _ => rfl) (by simp) (by simp) retained stackInside globalsInside
    · intro value same; cases same; trivial
    · simp [clearDictionary, found, object, Except.map]
    · simp [clearDictionary, moved, Except.map, relocateValue, relocateObject]
  all_goals
    apply Preserves.unchanged layout
    · simp [result, run, clearDictionary, found, object, Mutable.error, done, StepHeap]
    · simpa [result, run, clearDictionary, found, object, Mutable.error, done, StepWithin, CompletionWithin] using globalsInside
    · simp [result, run, clearDictionary, found, object, moved, Mutable.error, done, relocateStep, relocateCompletion, Except.map]

inductive DictionaryOperation : Operation → Prop
  | get (address : Nat) : DictionaryOperation (.dictionaryGet address)
  | setdefault (address : Nat) : DictionaryOperation (.dictionarySetDefault address)
  | clear (address : Nat) : DictionaryOperation (.dictionaryClear address)
  | store (address : Nat) : DictionaryOperation (.comprehensionStore address)

theorem step_dictionaryOperation_preserves (module : Module)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (operation : Operation) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (covered : DictionaryOperation operation)
    (inside : StateWithin ⟨.operation operation values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation operation values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation operation values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases covered with
  | get address =>
    rcases values with _ | ⟨key, _ | ⟨fallback, _ | ⟨extra, rest⟩⟩⟩
    case cons.nil =>
      exact (result_dictionaryGet_preserves logical physical rename logicalAnchors physicalAnchors
        address key (.scalar .none) stack globals layout inside.1.1 (inside.1.2 key (by simp))
        (by trivial) inside.2 globalsInside).protectGenerator stack inside.2
    case cons.cons.nil =>
      exact (result_dictionaryGet_preserves logical physical rename logicalAnchors physicalAnchors
        address key fallback stack globals layout inside.1.1 (inside.1.2 key (by simp))
        (inside.1.2 fallback (by simp)) inside.2 globalsInside).protectGenerator stack inside.2
    all_goals exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
      (some (.error ⟨"TypeError", []⟩)) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2
  | setdefault address =>
    rcases values with _ | ⟨key, _ | ⟨fallback, _ | ⟨extra, rest⟩⟩⟩
    case cons.nil =>
      exact (result_dictionarySetDefault_preserves logical physical rename logicalAnchors physicalAnchors
        address key (.scalar .none) stack globals layout inside.1.1 (inside.1.2 key (by simp))
        (by trivial) inside.2 globalsInside).protectGenerator stack inside.2
    case cons.cons.nil =>
      exact (result_dictionarySetDefault_preserves logical physical rename logicalAnchors physicalAnchors
        address key fallback stack globals layout inside.1.1 (inside.1.2 key (by simp))
        (inside.1.2 fallback (by simp)) inside.2 globalsInside).protectGenerator stack inside.2
    all_goals exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
      (some (.error ⟨"TypeError", []⟩)) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2
  | clear address =>
    cases values with
    | nil =>
      exact (result_clearDictionary_preserves logical physical rename logicalAnchors physicalAnchors
        address stack globals layout inside.1.1 inside.2 globalsInside).protectGenerator stack inside.2
    | cons value rest =>
      exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2
  | store address =>
    rcases values with _ | ⟨key, _ | ⟨value, _ | ⟨extra, rest⟩⟩⟩
    case cons.cons.nil =>
      exact (result_setItem_preserves logical physical rename logicalAnchors physicalAnchors
        (.ref address) key value stack globals layout inside.1.1 (inside.1.2 key (by simp))
        (inside.1.2 value (by simp)) inside.2 globalsInside).protectGenerator stack inside.2
    all_goals exact Preserves.unchanged layout (by trivial) (by trivial) rfl

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_dictionaryOperation_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (operation : Operation) (values : List Mutable.Value) (stack : List Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (covered : DictionaryOperation operation)
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
    (HeapCalls.Relocation.step_dictionaryOperation_preserves module logical physical rename logicalAnchors physicalAnchors
      operation values stack globals layout covered ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation

namespace FormalSW.PyAst.HeapCalls

/-- Bind the dictionary before argument effects, then read or insert in the resulting heap. -/
theorem Evaluates.dictionary_method {module : Module} {env : Env} {base : Expr}
    {heap middle afterArguments finalHeap : Mutable.Heap} {address : Nat} {expressions : List Expr}
    {values : List Value} {value : Value} {globals : Mutable.Globals} (insert : Bool)
    (receiver : Evaluates (globals := globals) module env base heap (.ref address) middle)
    (bound : bindMethod module (.ref address) (if insert then "setdefault" else "get") middle =
      some (.ok (if insert then .dictionarySetDefault address else .dictionaryGet address), middle))
    (arguments : Arguments (globals := globals) module env expressions middle values afterArguments)
    (operation : primitive (if insert then .dictionarySetDefault address else .dictionaryGet address) values afterArguments =
      some (.ok value, finalHeap))
    (localName : ∀ name, base = .name name → (env name).isSome = true) :
    Evaluates (globals := globals) module env
      (.call (.attribute base (if insert then "setdefault" else "get")) expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr base env,
    .methodReceiver (if insert then "setdefault" else "get") expressions env :: stack, heap⟩)
    (by cases insert <;> cases base <;> first | rfl | simp_all [step])
  apply (receiver anchors _).trans
  apply Reaches.next (following := argumentsState
    (if insert then .dictionarySetDefault address else .dictionaryGet address) env [] expressions stack middle)
    (by cases insert <;> simp_all [step, run])
  apply (Evaluates.arguments_reach arguments _ [] anchors stack).trans
  exact .next (by cases insert <;> simp_all [step, result, run]) .refl

end FormalSW.PyAst.HeapCalls
