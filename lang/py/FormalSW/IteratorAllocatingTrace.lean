import lang.py.FormalSW.IteratorExecutionIsolation

/-! Composable source traces with explicit allocations preserve private consumer objects. -/
namespace FormalSW.PyAst.IteratorCalls
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

/-- A live machine heap, excluding unsupported protocol completions which carry no heap. -/
def HeapAt (heap : Mutable.Heap) : State → Prop
  | .running core _ => core.core.heap = heap
  | .completed (.ok completion) _ _ => completion.heap = heap
  | .completed (.error _) _ _ => False

theorem HeapAt.stateHeap {heap : Mutable.Heap} {state : State} (atHeap : HeapAt heap state) :
    Relocation.StateHeap heap state := by
  cases state with
  | running => exact atHeap
  | completed outcome => cases outcome <;> first | exact atHeap | exact False.elim atHeap

theorem HeapAt.unique {heap other : Mutable.Heap} {state : State}
    (atHeap : HeapAt heap state) (otherHeap : Relocation.StateHeap other state) : other = heap := by
  cases state with
  | running => exact otherHeap.symm.trans atHeap
  | completed outcome =>
    cases outcome with
    | ok => exact otherHeap.symm.trans atHeap
    | error => exact False.elim atHeap

/-- Allocation cases describe actual source-machine operations. Stable segments may mutate,
call methods and consume choices. There is no bound on the number of allocations or segments. -/
inductive AllocatingTrace (module : Module) (anchors : Nat) (choices : ChoiceSchedule)
    (globals : Mutable.Globals) : Mutable.Heap → State → Mutable.Heap → State → Prop where
  | stable {before after first final}
      (firstHeap : HeapAt before first) (finalHeap : HeapAt after final)
      (sameSize : after.length = before.length)
      (ran : Reaches module anchors choices globals first final) :
      AllocatingTrace module anchors choices globals before first after final
  | list (heap : Mutable.Heap) (items : List Mutable.Value) (stack : List Frame)
      (used : Nat) (resumes : List Resume) :
      AllocatingTrace module anchors choices globals heap
        (.running ⟨⟨.operation .list items, stack, heap⟩, used⟩ resumes)
        (heap ++ [.list items])
        (.running ⟨⟨.value (.ref heap.length), stack, heap ++ [.list items]⟩, used⟩ resumes)
  | tuple (heap after : Mutable.Heap) (items : List Mutable.Value) (address : Nat)
      (stack : List Frame) (used : Nat) (resumes : List Resume)
      (allocated : Mutable.allocateTuple items heap = some (.ok (.ref address), after)) :
      AllocatingTrace module anchors choices globals heap
        (.running ⟨⟨.operation .tuple items, stack, heap⟩, used⟩ resumes) after
        (.running ⟨⟨.value (.ref address), stack, after⟩, used⟩ resumes)
  | newInstance (heap : Mutable.Heap) (name origin : String) (classBody : List Stmt)
      (stack : List Frame) (used : Nat) (resumes : List Resume)
      (noFunction : findFunctionIn module.body name = none)
      (noLibrary : libraryFunction module name = none)
      (defined : module.findClass name = some (origin, classBody))
      (noInitializer : findFunctionIn classBody "__init__" = none)
      (noDataclass : dataclassFields classBody = none) :
      AllocatingTrace module anchors choices globals heap
        (.running ⟨⟨.operation (.call name) [], stack, heap⟩, used⟩ resumes)
        (heap ++ [.instance origin name []])
        (.running ⟨⟨.value (.ref heap.length), stack, heap ++ [.instance origin name []]⟩, used⟩ resumes)
  | initializedInstance (heap : Mutable.Heap) (name origin : String) (classBody : List Stmt)
      (args : List Arg) (body : List Stmt) (values completed : List Mutable.Value)
      (stack : List Frame) (used : Nat) (resumes : List Resume)
      (noFunction : findFunctionIn module.body name = none)
      (noLibrary : libraryFunction module name = none)
      (defined : module.findClass name = some (origin, classBody))
      (initializer : findFunctionIn classBody "__init__" = some (args, body))
      (arguments : completeArguments args (.ref heap.length :: values) = some completed) :
      AllocatingTrace module anchors choices globals heap
        (.running ⟨⟨.operation (.call name) values, stack, heap⟩, used⟩ resumes)
        (heap ++ [.instance origin name []])
        (.running ⟨⟨.block (executableBody body) (functionEnv args body completed globals),
          .initialized heap.length :: stack, heap ++ [.instance origin name []]⟩, used⟩ resumes)
  | dataInstance (heap : Mutable.Heap) (name origin : String) (classBody : List Stmt)
      (frozen : Bool) (fields : List Arg) (values : List Mutable.Value)
      (stack : List Frame) (used : Nat) (resumes : List Resume)
      (noFunction : findFunctionIn module.body name = none)
      (noLibrary : libraryFunction module name = none)
      (defined : module.findClass name = some (origin, classBody))
      (noInitializer : findFunctionIn classBody "__init__" = none)
      (metadata : dataclassFields classBody = some (frozen, fields))
      (arity : fields.length = values.length) :
      AllocatingTrace module anchors choices globals heap
        (.running ⟨⟨.operation (.call name) values, stack, heap⟩, used⟩ resumes)
        (heap ++ [.dataInstance origin name frozen (fields.map Arg.name) ((fields.map Arg.name).zip values)])
        (.running ⟨⟨.value (.ref heap.length), stack,
          heap ++ [.dataInstance origin name frozen (fields.map Arg.name) ((fields.map Arg.name).zip values)]⟩, used⟩ resumes)
  | trans {before middle after first next final}
      (left : AllocatingTrace module anchors choices globals before first middle next)
      (right : AllocatingTrace module anchors choices globals middle next after final) :
      AllocatingTrace module anchors choices globals before first after final

theorem AllocatingTrace.heaps {module : Module} {anchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {before after : Mutable.Heap} {first final : State}
    (trace : AllocatingTrace module anchors choices globals before first after final) :
    HeapAt before first ∧ HeapAt after final := by
  induction trace with
  | stable firstHeap finalHeap => exact ⟨firstHeap, finalHeap⟩
  | list | tuple | newInstance | initializedInstance | dataInstance => exact ⟨rfl, rfl⟩
  | trans _ _ left right => exact ⟨left.1, right.2⟩

theorem AllocatingTrace.reaches {module : Module} {anchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {before after : Mutable.Heap} {first final : State}
    (trace : AllocatingTrace module anchors choices globals before first after final) :
    Reaches module anchors choices globals first final := by
  induction trace with
  | stable _ _ _ ran => exact ran
  | list => exact .next (core_next rfl rfl) .refl
  | tuple heap after items address stack used resumes allocated =>
    apply Reaches.next (core_next rfl ?_) .refl
    simp [SetCalls.step, SetCalls.liftStep, HeapCalls.step, primitive, result, run, allocated]
  | newInstance heap name origin classBody stack used resumes noFunction noLibrary defined noInitializer noDataclass =>
    apply Reaches.next (core_next rfl ?_) .refl
    simp [SetCalls.step, SetCalls.liftStep, HeapCalls.step, noFunction, noLibrary,
      construct, defined, noInitializer, noDataclass, result, run, Mutable.allocateInstance_result]
  | initializedInstance heap name origin classBody args body values completed stack used resumes noFunction noLibrary defined initializer arguments =>
    apply Reaches.next (core_next rfl ?_) .refl
    simp [SetCalls.step, SetCalls.liftStep, HeapCalls.step, noFunction, noLibrary,
      construct, defined, initializer, invokeMethod, arguments]
  | dataInstance heap name origin classBody frozen fields values stack used resumes noFunction noLibrary defined noInitializer metadata arity =>
    apply Reaches.next (core_next rfl ?_) .refl
    simp [SetCalls.step, SetCalls.liftStep, HeapCalls.step, noFunction, noLibrary,
      construct, defined, noInitializer, metadata, result, run, Mutable.allocateDataclass_result,
      show (fields.map Arg.name).length = values.length by simpa using arity]
  | trans _ _ left right => exact left.trans right

end FormalSW.PyAst.IteratorCalls
