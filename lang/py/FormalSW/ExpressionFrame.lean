import lang.py.FormalSW.ContinuationFrame

/-! Expression dispatch only prepares evaluation; it cannot mutate captured objects. -/
namespace FormalSW.PyAst.HeapCalls.Framing
open Mutable Mutable.Relocation
set_option Elab.async false

theorem step_expression_cell (module : Module) (address anchors : Nat) (object : Object)
    (heap : Heap) (expression : Expr) (env : Env) (stack : List Frame) (globals : Globals)
    (saved : SavedCell address object heap) :
    RetainsCell address object (step module anchors ⟨.expr expression env, stack, heap⟩ globals) := by
  unfold step
  apply protectGenerator_retains_cell address object stack
  with_reducible repeat' first
    | exact saved
    | trivial
    | (solve | simp only [RetainsCell, done, generatorArguments, truthGeneratorArguments,
        extremumGeneratorArguments, nextGeneratorArguments, argumentsState_heap, expandedArgumentsState_heap] <;> exact saved)
    | split

end FormalSW.PyAst.HeapCalls.Framing
