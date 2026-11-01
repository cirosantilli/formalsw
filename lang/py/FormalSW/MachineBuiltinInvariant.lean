import lang.py.FormalSW.MachineExpressionInvariant
import lang.py.FormalSW.MachineCallDispatchInvariant

/-! Builtin observations retain the execution invariant after argument effects. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- Length reads return scalars or errors without mutating the heap. -/
theorem length_scalar_result (heap : Mutable.Heap) (value : Value) :
    ∃ outcome : Option (Except ExceptionObject Constant),
      Mutable.length value heap = scalarResult outcome heap := by
  cases value with
  | scalar scalar =>
    refine ⟨some (Calls.length scalar), ?_⟩
    cases scalar <;> rfl
  | ref address =>
    cases found : heap[address]? with
    | none => exact ⟨none, by simp [Mutable.length, found, scalarResult, Mutable.unsupported]⟩
    | some object =>
      cases object with
      | list items | tuple items | bytearray items | set items | keySet items | dict items | keyDict items =>
        exact ⟨some (.ok (.int items.length)), by simp [Mutable.length, found, scalarResult]⟩
      | «instance» origin name fields | dataInstance origin name frozen declared fields =>
        exact ⟨some (.error ⟨"TypeError", []⟩), by simp [Mutable.length, found, scalarResult, Mutable.error]⟩

theorem length_effect (heap after : Mutable.Heap) (value : Value)
    (outcome : Except ExceptionObject Value)
    (executed : Mutable.length value heap = some (outcome, after)) :
    after = heap ∧ ∀ returned, outcome = .ok returned → ∃ scalar, returned = .scalar scalar := by
  obtain ⟨result, equation⟩ := length_scalar_result heap value
  rw [equation] at executed
  exact scalarResult_effect heap after result outcome executed

/-- This rule includes modeled errors and unsupported outcomes, without a completion premise. -/
theorem step_length_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (valueInside : value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.builtin .len) [value], stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.builtin .len) [value], stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have raw := result_readonly_preserves logical physical rename logicalAnchors physicalAnchors
    (Mutable.length value) (Mutable.length (relocateValue rename value)) stack globals layout stackInside globalsInside (by
      intro outcome after executed
      obtain ⟨same, scalar⟩ := length_effect logical after value outcome executed
      refine ⟨same, ?_⟩
      intro returned success
      obtain ⟨constant, rfl⟩ := scalar returned success
      trivial) (layout.runtime.length value valueInside)
  exact raw.protectGenerator stack stackInside

/-- Other arities retain the interpreter's unsupported outcome. -/
theorem step_length_arguments_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (values : List Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.builtin .len) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.builtin .len) values, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.builtin .len) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases values with
  | nil => apply Preserves.unchanged layout <;> trivial
  | cons value rest =>
    cases rest with
    | nil =>
      exact step_length_preserves module logical physical rename logicalAnchors physicalAnchors
        value stack globals layout (inside.1.2 value (by simp)) inside.2 globalsInside
    | cons next rest => apply Preserves.unchanged layout <;> trivial

/-- Digit testing observes text, bytes or the current buffer without changing it. -/
theorem isDigit_scalar_result (heap : Mutable.Heap) (receiver : Value) (values : List Value) :
    ∃ outcome : Option (Except ExceptionObject Constant),
      primitive (.isDigit receiver) values heap = scalarResult outcome heap := by
  cases values with
  | cons value rest =>
    refine ⟨some (.error ⟨"TypeError", []⟩), ?_⟩
    cases receiver with
    | scalar scalar => cases scalar <;> rfl
    | ref address => rfl
  | nil =>
    cases receiver with
    | scalar scalar =>
      cases scalar with
      | string text => exact ⟨some (.ok (.bool (Strings.isDigit text))), rfl⟩
      | bytes bytes => exact ⟨some (.ok (.bool (Py.Builtin.Bytes.isDigit bytes))), rfl⟩
      | int | bool | none => exact ⟨some (.error ⟨"TypeError", []⟩), rfl⟩
    | ref address =>
      cases found : heap[address]? with
      | none => exact ⟨none, by simp [primitive, found, scalarResult, Mutable.unsupported]⟩
      | some object =>
        cases object with
        | bytearray bytes =>
          exact ⟨some (.ok (.bool (Py.Builtin.Bytes.isDigit bytes))), by simp [primitive, found, scalarResult]⟩
        | _ => exact ⟨none, by simp [primitive, found, scalarResult, Mutable.unsupported]⟩

theorem isDigit_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (receiver : Value) (values : List Value)
    (inside : receiver.edge.Within logical.length) :
    primitive (.isDigit (relocateValue rename receiver)) (values.map (relocateValue rename)) physical =
      (primitive (.isDigit receiver) values logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  cases values with
  | cons value rest =>
    cases receiver with
    | scalar scalar => cases scalar <;> rfl
    | ref address => rfl
  | nil =>
    cases receiver with
    | scalar scalar => cases scalar <;> rfl
    | ref address =>
      have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
      have moved := layout.lookup address _ found
      cases object : logical[address] <;>
        simp only [object, relocateObject] at moved <;>
        simp [primitive, relocateValue, found, object, moved, Mutable.unsupported, Except.map]

theorem step_isDigit_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver : Value) (values : List Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.isDigit receiver) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.isDigit receiver) values, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.isDigit receiver) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have raw := result_readonly_preserves logical physical rename logicalAnchors physicalAnchors
    (primitive (.isDigit receiver) values)
    (primitive (.isDigit (relocateValue rename receiver)) (values.map (relocateValue rename)))
    stack globals layout inside.2 globalsInside (by
      intro outcome after executed
      obtain ⟨result, equation⟩ := isDigit_scalar_result logical receiver values
      rw [equation] at executed
      obtain ⟨same, scalar⟩ := scalarResult_effect logical after result outcome executed
      refine ⟨same, ?_⟩
      intro returned success
      obtain ⟨constant, rfl⟩ := scalar returned success
      trivial) (isDigit_relocates logical physical rename layout.runtime receiver values inside.1.1)
  exact raw.protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.HeapCalls

/-- Bind digit testing after receiver effects, then evaluate its arguments before execution. -/
theorem Evaluates.isDigit
    {module : Module} {globals : Mutable.Globals} {env : Env} {base : Expr}
    {expressions : List Expr} {heap afterReceiver afterArguments finalHeap : Mutable.Heap}
    {receiver value : Mutable.Value} {values : List Mutable.Value}
    (target : Evaluates (globals := globals) module env base heap receiver afterReceiver)
    (bound : bindMethod module receiver "isdigit" afterReceiver = some (.ok (.isDigit receiver), afterReceiver))
    (arguments : Evaluates.Arguments (globals := globals) module env expressions afterReceiver values afterArguments)
    (execution : primitive (.isDigit receiver) values afterArguments = some (.ok value, finalHeap)) :
    Evaluates (globals := globals) module env (.call (.attribute base "isdigit") expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr base env, .methodReceiver "isdigit" expressions env :: stack, heap⟩)
  · rw [Relocation.step_attribute_call]
    cases base with
    | name name => simp [target.name_isSome]
    | _ => rfl
  apply (target anchors _).trans
  apply Reaches.next (following := argumentsState (.isDigit receiver) env [] expressions stack afterReceiver)
    (by simp [step, run, bound])
  apply (Evaluates.arguments_reach arguments (.isDigit receiver) [] anchors stack).trans
  exact .next (by simp [step, result, run, execution]) .refl

end FormalSW.PyAst.HeapCalls
