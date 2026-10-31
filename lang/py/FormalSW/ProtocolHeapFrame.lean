import lang.py.FormalSW.AcquisitionHeapFrame
import lang.py.FormalSW.ProtocolCalls

/-! Protocol binding and iterator-result validation preserve arbitrary heap predicates. -/
namespace FormalSW.PyAst.Heapq
open Mutable
set_option Elab.async false

theorem preserves_protocolLookup (invariant : Heap → Prop) (module : Module)
    (receiver : Value) (name : String) :
    Preserves invariant (ProtocolCalls.lookup module receiver name) := by
  unfold ProtocolCalls.lookup
  with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_instanceClass invariant _ _ _); intro body
    | split

theorem preserves_nextMethod (invariant : Heap → Prop) (module : Module) (receiver : Value) :
    Preserves invariant (ProtocolCalls.nextMethod module receiver) := by
  unfold ProtocolCalls.nextMethod
  with_reducible repeat' first
    | exact preserves_protocolLookup invariant _ _ _
    | exact Preserves.pure invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | split

theorem preserves_iterMethod (invariant : Heap → Prop) (module : Module) (receiver : Value) :
    Preserves invariant (ProtocolCalls.iterMethod module receiver) := by
  unfold ProtocolCalls.iterMethod
  with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (preserves_protocolLookup invariant _ _ _); intro operation
    | split

theorem iterFinish_preserves (invariant : Heap → Prop) (module : Module)
    (completion checked : Completion) (saved : invariant completion.heap)
    (finished : ProtocolCalls.iterFinish module completion = some checked) : invariant checked.heap := by
  rcases completion with ⟨outcome, globals, heap, anchors⟩
  cases outcome with
  | error error =>
    simp only [ProtocolCalls.iterFinish, Option.some.injEq] at finished
    subst checked
    exact saved
  | ok value =>
    cases executed : ProtocolCalls.nextMethod module value heap with
    | none => simp [ProtocolCalls.iterFinish, executed] at finished
    | some pair =>
      rcases pair with ⟨outcome, after⟩
      have retained := preserves_nextMethod invariant module value heap outcome after saved executed
      cases outcome with
      | error error =>
        simp only [ProtocolCalls.iterFinish, executed, Option.some.injEq] at finished
        subst checked
        exact retained
      | ok operation =>
        cases operation <;> simp only [ProtocolCalls.iterFinish, executed, Option.some.injEq] at finished
        all_goals subst checked; exact retained

end FormalSW.PyAst.Heapq
