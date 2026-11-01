import lang.py.FormalSW.ClassCalls

/-! Implicit protocol lookup bypasses instance fields and executes the class method body.
Acquisition and advancement expose method calls independently of loop consumers. -/
namespace FormalSW.PyAst.ProtocolCalls
open HeapCalls
set_option Elab.async false

/-- Plain source classes have fixed namespaces and no descriptors or inheritance. -/
def lookup (module : Module) (receiver : Mutable.Value) (name : String) :
    Mutable.Eval (Option Operation) := do
  match receiver with
  | .ref address =>
      match (← get)[address]? with
      | some (.instance origin className _) | some (.dataInstance origin className _ _ _) =>
          let body ← instanceClass module origin className
          pure ((findFunctionIn body name).map fun (args, code) => .method receiver args code)
      | _ => Mutable.unsupported
  | .scalar _ => Mutable.unsupported

theorem lookup_instance (module : Module) (heap : Mutable.Heap) (address : Nat)
    (origin className name : String) (fields : List (String × Mutable.Value))
    (body : List Stmt) (found : heap[address]? = some (.instance origin className fields))
    (defined : module.findClass className = some (origin, body)) :
    lookup module (.ref address) name heap = some (.ok
      ((findFunctionIn body name).map fun (args, code) => .method (.ref address) args code), heap) := by
  simp [lookup, instanceClass, found, defined, Except.map]

theorem lookup_data_instance (module : Module) (heap : Mutable.Heap) (address : Nat)
    (origin className name : String) (frozen : Bool) (declared : List String)
    (fields : List (String × Mutable.Value)) (body : List Stmt)
    (found : heap[address]? = some (.dataInstance origin className frozen declared fields))
    (defined : module.findClass className = some (origin, body)) :
    lookup module (.ref address) name heap = some (.ok
      ((findFunctionIn body name).map fun (args, code) => .method (.ref address) args code), heap) := by
  simp [lookup, instanceClass, found, defined, Except.map]

/-- None of the supported scalar or container values is itself a next-able iterator. -/
def nextMethod (module : Module) (receiver : Mutable.Value) : Mutable.Eval (Option Operation) := do
  match receiver with
  | .scalar _ => pure none
  | .ref address =>
      match (← get)[address]? with
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) =>
          lookup module receiver "__next__"
      | some _ => pure none
      | none => Mutable.unsupported

inductive State where
  | start (receiver : Mutable.Value) (heap : Mutable.Heap)
  | running (core : HeapCalls.State)

def lift : Step HeapCalls.State Mutable.Completion → Step State Mutable.Completion
  | .next core => .next (.running core)
  | .done outcome => .done outcome
  | .unsupported => .unsupported

/-- StopIteration remains observable here; a consuming loop must handle its own exhaustion. -/
def step (module : Module) (anchors : Nat) (state : State)
    (globals : Mutable.Globals := []) : Step State Mutable.Completion :=
  match state with
  | .start receiver heap => lift <|
      run (globals := globals) anchors heap (nextMethod module receiver) fun method heap =>
        match method with
        | none => done (globals := globals) anchors heap
            (.error { typeName := "TypeError", args := [] })
        | some operation => .next ⟨.operation operation [], [], heap⟩
  | .running core => lift (HeapCalls.step (globals := globals) module anchors core)

def next (module : Module) (receiver : Mutable.Value) (heap : Mutable.Heap)
    (globals : Mutable.Globals := []) : Mutable.Call :=
  ⟨⟨State, .start receiver heap, step (globals := globals) module heap.length⟩⟩

theorem finishes_running {module : Module} {anchors : Nat} {state : HeapCalls.State}
    {outcome : Except ExceptionObject Mutable.Completion} {globals : Mutable.Globals}
    (finished : Finishes (HeapCalls.step (globals := globals) module anchors) state outcome) :
    Finishes (step (globals := globals) module anchors) (.running state) outcome := by
  induction finished with
  | done terminal => exact .done (by simp [step, terminal, lift])
  | next transition _ ih => exact .next (by simp [step, transition, lift]) ih

/-- Actual method execution, including effects before an exceptional exit, is retained. -/
theorem next_finishes (module : Module) (receiver : Mutable.Value) (heap : Mutable.Heap)
    (operation : Operation) (globals : Mutable.Globals) (outcome : Mutable.Completion)
    (bound : nextMethod module receiver heap = some (.ok (some operation), heap))
    (finished : Finishes (HeapCalls.step (globals := globals) module heap.length)
      ⟨.operation operation [], [], heap⟩ (.ok outcome)) :
    (next module receiver heap globals).Finishes outcome := by
  change Finishes (step (globals := globals) module heap.length)
    (.start receiver heap) (.ok outcome)
  exact .next (following := .running ⟨.operation operation [], [], heap⟩)
    (by simp [step, run, bound, lift]) (finishes_running finished)

/-- A successful next call returns the method's value and keeps its actual shared-heap writes. -/
theorem next_returns (module : Module) (receiver : Mutable.Value) (heap after : Mutable.Heap)
    (args : List Arg) (body : List Stmt) (value : Mutable.Value) (globals : Mutable.Globals)
    (bound : nextMethod module receiver heap =
      some (.ok (some (.method receiver args body)), heap))
    (executed : MethodReturns module receiver args body [] heap value after globals) :
    (next module receiver heap globals).Finishes ⟨.ok value, globals, after, heap.length⟩ :=
  next_finishes module receiver heap _ globals _ bound
    ((executed heap.length []).finishes (.done rfl))

/-- A missing __iter__ may require Python's sequence fallback, which stays unsupported here. -/
def iterMethod (module : Module) (receiver : Mutable.Value) : Mutable.Eval Operation := do
  match ← lookup module receiver "__iter__" with
  | some operation => pure operation
  | none =>
      match ← lookup module receiver "__getitem__" with
      | some _ => Mutable.unsupported
      | none => Mutable.error "TypeError"

/-- __iter__ must return an iterator; this check does not advance it. -/
def iterFinish (module : Module) (completion : Mutable.Completion) : Option Mutable.Completion :=
  match completion.outcome with
  | .error _ => some completion
  | .ok value =>
      match nextMethod module value completion.heap with
      | none => none
      | some (.ok (some _), heap) => some { completion with heap := heap }
      | some (.ok none, heap) => some { completion with
          heap := heap
          outcome := .error { typeName := "TypeError", args := [] } }
      | some (.error error, heap) => some { completion with heap := heap, outcome := .error error }

inductive IterState where
  | start (receiver : Mutable.Value) (heap : Mutable.Heap)
  | running (core : HeapCalls.State)

def iterLift : Step HeapCalls.State Mutable.Completion → Step IterState Mutable.Completion
  | .next core => .next (.running core)
  | .done outcome => .done outcome
  | .unsupported => .unsupported

def iterStep (module : Module) (anchors : Nat) (state : IterState)
    (globals : Mutable.Globals := []) : Step IterState Mutable.Completion :=
  match state with
  | .start receiver heap => iterLift <|
      run (globals := globals) anchors heap (iterMethod module receiver) fun operation heap =>
        .next ⟨.operation operation [], [], heap⟩
  | .running core =>
      match HeapCalls.step (globals := globals) module anchors core with
      | .done (.ok completion) =>
          match iterFinish module completion with
          | some checked => .done (.ok checked)
          | none => .unsupported
      | other => iterLift other

def iter (module : Module) (receiver : Mutable.Value) (heap : Mutable.Heap)
    (globals : Mutable.Globals := []) : Mutable.Call :=
  ⟨⟨IterState, .start receiver heap, iterStep (globals := globals) module heap.length⟩⟩

theorem iter_finishes_running {module : Module} {anchors : Nat} {state : HeapCalls.State}
    {completion checked : Mutable.Completion} {globals : Mutable.Globals}
    (finished : Finishes (HeapCalls.step (globals := globals) module anchors) state (.ok completion))
    (validated : iterFinish module completion = some checked) :
    Finishes (iterStep (globals := globals) module anchors) (.running state) (.ok checked) := by
  generalize outcome_eq : Except.ok completion = outcome at finished
  induction finished with
  | done terminal =>
      rw [← outcome_eq] at terminal
      exact .done (by simp [iterStep, terminal, validated])
  | next transition _ ih =>
      exact .next (by simp [iterStep, transition, iterLift]) (ih outcome_eq)

theorem iter_finishes (module : Module) (receiver : Mutable.Value) (heap : Mutable.Heap)
    (operation : Operation) (globals : Mutable.Globals) (completion checked : Mutable.Completion)
    (bound : iterMethod module receiver heap = some (.ok operation, heap))
    (finished : Finishes (HeapCalls.step (globals := globals) module heap.length)
      ⟨.operation operation [], [], heap⟩ (.ok completion))
    (validated : iterFinish module completion = some checked) :
    (iter module receiver heap globals).Finishes checked := by
  change Finishes (iterStep (globals := globals) module heap.length)
    (.start receiver heap) (.ok checked)
  exact .next (following := .running ⟨.operation operation [], [], heap⟩)
    (by simp [iterStep, run, bound, iterLift]) (iter_finishes_running finished validated)

/-- Acquisition preserves method effects and validates the returned object's next slot. -/
theorem iter_returns (module : Module) (receiver : Mutable.Value) (heap after : Mutable.Heap)
    (args : List Arg) (body : List Stmt) (value : Mutable.Value) (advance : Operation)
    (globals : Mutable.Globals)
    (bound : iterMethod module receiver heap = some (.ok (.method receiver args body), heap))
    (executed : MethodReturns module receiver args body [] heap value after globals)
    (iterator : nextMethod module value after = some (.ok (some advance), after)) :
    (iter module receiver heap globals).Finishes ⟨.ok value, globals, after, heap.length⟩ :=
  iter_finishes module receiver heap _ globals _ _ bound
    ((executed heap.length []).finishes (.done rfl)) (by simp [iterFinish, iterator])

end FormalSW.PyAst.ProtocolCalls
