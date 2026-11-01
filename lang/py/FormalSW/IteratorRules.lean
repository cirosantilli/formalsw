import lang.py.FormalSW.IteratorLifting

/-! Source-level protocol and loop composition with actual method execution and shared mutations. -/
namespace FormalSW.PyAst.IteratorCalls
open HeapCalls
set_option Elab.async false

variable {module : Module} {choices : ChoiceSchedule} {globals : Mutable.Globals} {used : Nat}

/-- Method execution stops at its protocol boundary, before the consuming loop resumes. -/
def OperationCompletes (module : Module) (choices : ChoiceSchedule) (used : Nat)
    (operation : Operation)
    (heap : Mutable.Heap) (outcome : Except ExceptionObject Mutable.Value)
    (after : Mutable.Heap) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors resumes, ∃ finalUsed,
    Reaches module anchors choices globals
      (.running ⟨⟨.operation operation [], [], heap⟩, used⟩ resumes)
      (.completed (.ok ⟨outcome, globals, after, anchors⟩) finalUsed resumes)

theorem Reaches.of_heap {anchors used : Nat} {first final : HeapCalls.State}
    (before : HeapCalls.Reaches module anchors first final (globals := globals))
    (resumes : List Resume) :
    Reaches module anchors choices globals (.running ⟨first, used⟩ resumes)
      (.running ⟨final, used⟩ resumes) :=
  Reaches.of_set (SetCalls.Reaches.of_heap before choices used) resumes

theorem OperationCompletes.of_method {receiver : Mutable.Value} {args : List Arg}
    {body : List Stmt} {heap after : Mutable.Heap} {value : Mutable.Value}
    (executed : MethodReturns module receiver args body [] heap value after globals) :
    OperationCompletes module choices used (.method receiver args body) heap (.ok value) after globals := by
  intro anchors resumes
  refine ⟨used, (Reaches.of_heap (executed anchors []) resumes).trans ?_⟩
  exact .next (core_done rfl rfl) .refl

/-- Existing source exception proofs can also supply protocol execution, retaining all writes. -/
theorem OperationCompletes.of_heap {operation : Operation} {heap after : Mutable.Heap}
    {outcome : Except ExceptionObject Mutable.Value}
    (executed : ∀ anchors, Finishes (HeapCalls.step module anchors · globals)
      ⟨.operation operation [], [], heap⟩ (.ok ⟨outcome, globals, after, anchors⟩))
    (safe : outcome ≠ .error ⟨"TypeError", []⟩) :
    OperationCompletes module choices used operation heap outcome after globals := by
  intro anchors resumes
  apply completion_of_set
    (SetCalls.finishes_of_heap (executed anchors) choices used) _ resumes
  intro completion same
  cases same
  exact safe

variable {anchors : Nat} {heap after : Mutable.Heap} {loop : Loop}
  {resumes : List Resume} {receiver iterator value : Mutable.Value} {operation advance : Operation}

theorem acquire_returns
    (isObject : isInstance heap receiver = true)
    (bound : ProtocolCalls.iterMethod module receiver heap = some (.ok operation, heap))
    (executed : OperationCompletes module choices used operation heap (.ok iterator) after globals)
    (valid : ProtocolCalls.nextMethod module iterator after =
      some (.ok (some advance), after)) :
    ∃ finalUsed, Reaches module anchors choices globals
      (.running ⟨⟨.value receiver,
        .sequence loop.name loop.body loop.otherwise loop.following loop.env :: loop.stack,
        heap⟩, used⟩ resumes)
      (.running ⟨⟨.block (loopCode loop iterator :: loop.following) loop.env,
        loop.stack, after⟩, finalUsed⟩ resumes) := by
  obtain ⟨finalUsed, called⟩ := executed anchors (.acquire loop :: resumes)
  refine ⟨finalUsed, ?_⟩
  apply Reaches.next (following := .running ⟨⟨.operation operation [], [], heap⟩, used⟩
    (.acquire loop :: resumes))
  · simp [step, intercept, isObject, enter, bound]
  · exact acquired called valid

theorem advance_returns
    (isObject : isInstance heap iterator = true)
    (bound : ProtocolCalls.nextMethod module iterator heap = some (.ok (some operation), heap))
    (executed : OperationCompletes module choices used operation heap (.ok value) after globals) :
    ∃ finalUsed, Reaches module anchors choices globals
      (.running ⟨⟨.block (loopCode loop iterator :: loop.following) loop.env,
        loop.stack, heap⟩, used⟩ resumes)
      (.running ⟨⟨.block (loop.body ++ [Calls.loopContinuation loop.body (loopCode loop iterator)]
        ++ loop.following) (setLocal loop.env loop.name value),
        loop.stack, after⟩, finalUsed⟩ resumes) := by
  obtain ⟨finalUsed, called⟩ := executed anchors (.advance loop iterator :: resumes)
  refine ⟨finalUsed, ?_⟩
  apply Reaches.next (following := .running ⟨⟨.operation operation [], [], heap⟩, used⟩
    (.advance loop iterator :: resumes))
  · simp [step, intercept, loopCode, isObject, enter, bound]
  · exact advanced called

theorem advance_exhausted {args : List Constant}
    (isObject : isInstance heap iterator = true)
    (bound : ProtocolCalls.nextMethod module iterator heap = some (.ok (some operation), heap))
    (executed : OperationCompletes module choices used operation heap
      (.error ⟨"StopIteration", args⟩) after globals) :
    ∃ finalUsed, Reaches module anchors choices globals
      (.running ⟨⟨.block (loopCode loop iterator :: loop.following) loop.env,
        loop.stack, heap⟩, used⟩ resumes)
      (.running ⟨⟨.block (loop.otherwise ++ loop.following) loop.env,
        loop.stack, after⟩, finalUsed⟩ resumes) := by
  obtain ⟨finalUsed, called⟩ := executed anchors (.advance loop iterator :: resumes)
  refine ⟨finalUsed, ?_⟩
  apply Reaches.next (following := .running ⟨⟨.operation operation [], [], heap⟩, used⟩
    (.advance loop iterator :: resumes))
  · simp [step, intercept, loopCode, isObject, enter, bound]
  · exact exhausted called

/-- An ordinary advancement failure escapes the loop with the method's final heap. -/
theorem advance_failed {error : ExceptionObject}
    (isObject : isInstance heap iterator = true)
    (bound : ProtocolCalls.nextMethod module iterator heap = some (.ok (some operation), heap))
    (executed : OperationCompletes module choices used operation heap (.error error) after globals)
    (notExhausted : error.typeName ≠ "StopIteration") :
    ∃ finalUsed, Reaches module anchors choices globals
      (.running ⟨⟨.block (loopCode loop iterator :: loop.following) loop.env,
        loop.stack, heap⟩, used⟩ resumes)
      (.completed (.ok ⟨.error error, globals, after, anchors⟩) finalUsed resumes) := by
  obtain ⟨finalUsed, called⟩ := executed anchors (.advance loop iterator :: resumes)
  refine ⟨finalUsed, ?_⟩
  apply Reaches.next (following := .running ⟨⟨.operation operation [], [], heap⟩, used⟩
    (.advance loop iterator :: resumes))
  · simp [step, intercept, loopCode, isObject, enter, bound]
  · apply called.trans
    exact .next (by simp [step, resume, notExhausted, propagate, Calls.generatorException]) .refl

/-- StopIteration from acquisition is an exception, not exhaustion of the loop. -/
theorem acquire_failed {error : ExceptionObject}
    (isObject : isInstance heap receiver = true)
    (bound : ProtocolCalls.iterMethod module receiver heap = some (.ok operation, heap))
    (executed : OperationCompletes module choices used operation heap (.error error) after globals) :
    ∃ finalUsed, Reaches module anchors choices globals
      (.running ⟨⟨.value receiver,
        .sequence loop.name loop.body loop.otherwise loop.following loop.env :: loop.stack,
        heap⟩, used⟩ resumes)
      (.completed (.ok ⟨.error (Calls.generatorException (loop.stack.any Frame.inGenerator) error),
        globals, after, anchors⟩) finalUsed resumes) := by
  obtain ⟨finalUsed, called⟩ := executed anchors (.acquire loop :: resumes)
  refine ⟨finalUsed, ?_⟩
  apply Reaches.next (following := .running ⟨⟨.operation operation [], [], heap⟩, used⟩
    (.acquire loop :: resumes))
  · simp [step, intercept, isObject, enter, bound]
  · exact called.trans (.next rfl .refl)

/-- A normally completing loop body may mutate or allocate arbitrary shared objects. -/
theorem advance_continue {finalEnv : HeapCalls.Env} {finalHeap : Mutable.Heap}
    (isObject : isInstance heap iterator = true)
    (bound : ProtocolCalls.nextMethod module iterator heap = some (.ok (some operation), heap))
    (executed : OperationCompletes module choices used operation heap (.ok value) after globals)
    (noTransfer : Calls.loopControl loop.body = false)
    (body : BlockContinues module (setLocal loop.env loop.name value) loop.body
      after finalEnv finalHeap globals) :
    ∃ finalUsed, Reaches module anchors choices globals
      (.running ⟨⟨.block (loopCode loop iterator :: loop.following) loop.env,
        loop.stack, heap⟩, used⟩ resumes)
      (.running ⟨⟨.block (loopCode loop iterator :: loop.following) finalEnv,
        loop.stack, finalHeap⟩, finalUsed⟩ resumes) := by
  obtain ⟨finalUsed, yielded⟩ := advance_returns (loop := loop) (resumes := resumes)
    (anchors := anchors) (used := used) isObject bound executed
  refine ⟨finalUsed, yielded.trans ?_⟩
  simpa only [Calls.loopContinuation, noTransfer, Bool.false_eq_true, ↓reduceIte,
    List.append_assoc, List.singleton_append] using Reaches.of_heap (choices := choices) (used := finalUsed)
      (body (loopCode loop iterator :: loop.following) anchors loop.stack) resumes

/-- Evaluate the iterable once, then execute and validate the source acquisition method. -/
theorem for_instance {source : Expr} {entry : Mutable.Heap}
    (ordinary : ∀ args, source ≠ .call (.name "range") args)
    (evaluated : Evaluates module loop.env source entry receiver heap globals)
    (isObject : isInstance heap receiver = true)
    (bound : ProtocolCalls.iterMethod module receiver heap = some (.ok operation, heap))
    (executed : OperationCompletes module choices used operation heap (.ok iterator) after globals)
    (valid : ProtocolCalls.nextMethod module iterator after =
      some (.ok (some advance), after)) :
    ∃ finalUsed, Reaches module anchors choices globals
      (.running ⟨⟨.block (.forIn (.name loop.name) source loop.body loop.otherwise ::
        loop.following) loop.env, loop.stack, entry⟩, used⟩ resumes)
      (.running ⟨⟨.block (loopCode loop iterator :: loop.following) loop.env,
        loop.stack, after⟩, finalUsed⟩ resumes) := by
  obtain ⟨finalUsed, acquired⟩ := acquire_returns (loop := loop) (anchors := anchors)
    (used := used) (resumes := resumes) isObject bound executed valid
  refine ⟨finalUsed, ?_⟩
  apply Reaches.trans _ (Reaches.trans (Reaches.of_heap (evaluated anchors _) resumes) acquired)
  apply Reaches.of_heap
  apply HeapCalls.Reaches.next (following :=
    ⟨.expr source loop.env, .sequence loop.name loop.body loop.otherwise loop.following
      loop.env :: loop.stack, entry⟩)
  · have notPermutations := evaluated.not_permutations
    have notCombinations := evaluated.not_combinations
    have notValues := evaluated.not_dictionary_values
    cases source <;> simp_all [HeapCalls.step]
  · exact .refl

end FormalSW.PyAst.IteratorCalls

namespace FormalSW.PyAst.HeapCalls

/-- Linked protocol classes do not change an already supported source execution. -/
theorem finishes_extend {target source : Module} {anchors : Nat} {state : State}
    {globals : Mutable.Globals} {outcome : Except ExceptionObject Mutable.Completion}
    (finished : Finishes (step source anchors · globals) state outcome)
    (extension : Extends target source) :
    Finishes (step target anchors · globals) state outcome := by
  induction finished with
  | done terminal =>
      exact .done (by rw [step_extend extension _ (by simp [terminal])]; exact terminal)
  | next transition _ ih =>
      exact .next (by rw [step_extend extension _ (by simp [transition])]; exact transition) ih

theorem BlockContinues.extend {target source : Module} {env finalEnv : Env}
    {body : List Stmt} {heap after : Mutable.Heap} {globals : Mutable.Globals}
    (executed : BlockContinues source env body heap finalEnv after globals)
    (extension : Extends target source) :
    BlockContinues target env body heap finalEnv after globals :=
  fun following anchors stack => (executed following anchors stack).extend extension

end FormalSW.PyAst.HeapCalls
