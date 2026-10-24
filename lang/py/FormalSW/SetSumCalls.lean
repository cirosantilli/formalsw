import lang.py.FormalSW.SetCalls

/-! Summation of scalar sets is independent of every iterator choice.

The interpreter still selects arbitrary unvisited representatives. Integer and
Boolean additions use the ordinary heap interpreter; these proofs neither sort
the set nor replace its iteration with a preferred order. -/
namespace FormalSW.PyAst.SetCalls
open HeapCalls
variable {globals : Mutable.Globals}

/-- The scalar types that participate in exact integer addition. -/
def Numeric : Constant → Prop
  | .int _ | .bool _ => True
  | _ => False

def numericValue : Constant → Int
  | .int n => n
  | .bool b => if b then 1 else 0
  | _ => 0

private theorem numeric_add (item : Constant) (numeric : Numeric item) (total : Int)
    (heap : Mutable.Heap) :
    Mutable.binary .add (.scalar (.int total)) (.scalar item) heap =
      some (.ok (.scalar (.int (total + numericValue item))), heap) := by
  cases item <;> simp only [Numeric] at numeric
  all_goals try contradiction
  case int => rfl
  case bool value => cases value <;> rfl

/-- Removing whichever element the schedule selected preserves the total. -/
private theorem sum_eraseIdx (number : α → Int) (items : List α) (index : Nat)
    (bound : index < items.length) :
    number items[index] + ((items.eraseIdx index).map number).sum = (items.map number).sum := by
  induction items generalizing index with
  | nil => simp at bound
  | cons head tail ih =>
      cases index with
      | zero => simp
      | succ index =>
          have tailBound : index < tail.length := by simpa using bound
          have rest := ih index tailBound
          simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ, List.map_cons, List.sum_cons]
          omega

/-- The internal sum loop returns the same exact value under every choice schedule. -/
theorem sum_numeric_loop (choices : ChoiceSchedule) (module : Module)
    (heap : Mutable.Heap) (address : Nat) (original remaining : List Constant)
    (found : heap[address]? = some (.set original))
    (numeric : ∀ item ∈ remaining, Numeric item)
    (total : Int) (env : HeapCalls.Env)
    (accumulator : env sumAccumulator = some (.scalar (.int total)))
    (anchors : Nat) (stack : List HeapCalls.Frame) (used : Nat) :
    ∃ finalUsed, Reaches choices module anchors
      ⟨⟨.block [.setStepLoop sumItem address original remaining (sumBody (.name sumItem) []) [],
        .return (.name sumAccumulator)] env, stack, heap⟩, used⟩
      ⟨⟨.value (.scalar (.int (total + (remaining.map numericValue).sum))), stack, heap⟩, finalUsed⟩
      (globals := globals) := by
  cases remainingEq : remaining with
  | nil =>
      refine ⟨used, .next (following :=
        ⟨⟨.block [.return (.name sumAccumulator)] env, stack, heap⟩, used⟩) ?_ ?_⟩
      · simp [step, HeapCalls.step, iteratorStep, found]
      · simpa using Reaches.of_heap
          ((HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup accumulator)) anchors stack)
          choices used
  | cons head tail =>
      simp only [remainingEq] at numeric
      let index := choices used % (head :: tail).length
      have bound : index < (head :: tail).length := Nat.mod_lt _ (by simp)
      let item := (head :: tail)[index]
      have selected : (head :: tail)[index]? = some item := List.getElem?_eq_getElem bound
      have selected' : (head :: tail)[choices used % (tail.length + 1)]? = some item := selected
      let rest := (head :: tail).eraseIdx index
      let boundEnv := setLocal env sumItem (.scalar item)
      let updatedEnv := setLocal boundEnv sumAccumulator (.scalar (.int (total + numericValue item)))
      have emitted : HeapCalls.BlockContinues (globals := globals) module boundEnv
          (sumBody (.name sumItem) []) heap updatedEnv heap := by
        apply HeapCalls.BlockContinues.assign
        apply HeapCalls.Evaluates.binary
          (av := .scalar (.int total)) (bv := .scalar item) (middle := heap) (afterRight := heap)
        · exact HeapCalls.Evaluates.lookup (by simpa [boundEnv, setLocal, sumItem, sumAccumulator] using accumulator)
        · exact HeapCalls.Evaluates.lookup (by simp [boundEnv, setLocal])
        · exact numeric_add item (numeric item (List.getElem_mem bound)) total heap
      obtain ⟨finalUsed, completed⟩ := sum_numeric_loop choices module heap address original rest found
        (fun value member => numeric value (List.mem_of_mem_eraseIdx member))
        (total + numericValue item) updatedEnv (by simp [updatedEnv, setLocal]) anchors stack (used + 1)
      refine ⟨finalUsed, .next (following :=
        ⟨⟨.block (sumBody (.name sumItem) [] ++
          [.setStepLoop sumItem address original rest (sumBody (.name sumItem) []) [],
            .return (.name sumAccumulator)]) boundEnv, stack, heap⟩, used + 1⟩) ?_ ?_⟩
      · simp [step, HeapCalls.step, iteratorStep, found, selected', index, sumBody,
          Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, rest, boundEnv]
      · have path := Reaches.of_heap
          (emitted [.setStepLoop sumItem address original rest (sumBody (.name sumItem) []) [],
            .return (.name sumAccumulator)] anchors stack) choices (used + 1)
        have conservation := sum_eraseIdx numericValue (head :: tail) index bound
        have same : total + numericValue item + (rest.map numericValue).sum =
            total + ((head :: tail).map numericValue).sum := by
          exact (Int.add_assoc ..).trans (congrArg (fun n => total + n) conservation)
        rw [same] at completed
        exact path.trans completed
termination_by remaining.length
decreasing_by
  simp only [remainingEq]
  change ((head :: tail).eraseIdx index).length < (head :: tail).length
  rw [List.length_eraseIdx_of_lt bound]
  simp

/-- Sum an existing numeric set from an integer starting value. -/
theorem sum_numeric_reaches (choices : ChoiceSchedule) (module : Module)
    (heap : Mutable.Heap) (address : Nat) (items : List Constant)
    (found : heap[address]? = some (.set items))
    (numeric : ∀ item ∈ items, Numeric item) (initial : Int)
    (anchors : Nat) (stack : List HeapCalls.Frame) (used : Nat) :
    ∃ finalUsed, Reaches choices module anchors
      ⟨⟨.operation .sumSequence [.ref address, .scalar (.int initial)], stack, heap⟩, used⟩
      ⟨⟨.value (.scalar (.int (initial + (items.map numericValue).sum))), stack, heap⟩, finalUsed⟩
      (globals := globals) := by
  obtain ⟨finalUsed, loop⟩ := sum_numeric_loop (globals := globals) choices module heap address items items
    found numeric initial (setLocal (fun _ => none) sumAccumulator (.scalar (.int initial)))
    (by simp [setLocal]) anchors stack used
  refine ⟨finalUsed, .next ?_ loop⟩
  simp [step, HeapCalls.step, sumSequenceStart, run, Mutable.sequence, found, Mutable.unsupported,
    iteratorStep, sumEnter, sumInitial, liftStep]

theorem sum_integers_reaches (choices : ChoiceSchedule) (module : Module)
    (heap : Mutable.Heap) (address : Nat) (items : List Int)
    (found : heap[address]? = some (.set (items.map Constant.int))) (initial : Int)
    (anchors : Nat) (stack : List HeapCalls.Frame) (used : Nat) :
    ∃ finalUsed, Reaches choices module anchors
      ⟨⟨.operation .sumSequence [.ref address, .scalar (.int initial)], stack, heap⟩, used⟩
      ⟨⟨.value (.scalar (.int (initial + items.sum))), stack, heap⟩, finalUsed⟩
      (globals := globals) := by
  have result := sum_numeric_reaches (globals := globals) choices module heap address
    (items.map Constant.int) found (by simp [Numeric]) initial anchors stack used
  simpa [List.map_map, Function.comp_def, numericValue] using result

/-- Expression evaluation remains compositional while quantifying over all choices. -/
def Evaluates (module : Module) (env : HeapCalls.Env) (expression : Expr)
    (heap : Mutable.Heap) (value : Mutable.Value) (finalHeap : Mutable.Heap)
    (globals : Mutable.Globals := []) : Prop :=
  ∀ choices anchors stack used, ∃ finalUsed, Reaches choices module anchors
    ⟨⟨.expr expression env, stack, heap⟩, used⟩ ⟨⟨.value value, stack, finalHeap⟩, finalUsed⟩
    (globals := globals)

theorem Evaluates.of_heap
    (evaluated : HeapCalls.Evaluates (globals := globals) module env expression heap value finalHeap) :
    Evaluates module env expression heap value finalHeap (globals := globals) :=
  fun choices anchors stack used => ⟨used, Reaches.of_heap (evaluated anchors stack) choices used⟩

theorem Evaluates.sum_integers {items : List Int}
    (arguments : HeapCalls.Evaluates.Arguments (globals := globals) module env [iterable, start]
      heap [.ref address, .scalar (.int initial)] middle)
    (found : middle[address]? = some (.set (items.map Constant.int))) :
    Evaluates module env (.sumSequence iterable start) heap
      (.scalar (.int (initial + items.sum))) middle (globals := globals) := by
  intro choices anchors stack used
  obtain ⟨finalUsed, sum⟩ := sum_integers_reaches (globals := globals) choices module middle address items
    found initial anchors stack used
  refine ⟨finalUsed, .next rfl ?_⟩
  exact (Reaches.of_heap (HeapCalls.Evaluates.arguments_reach arguments _ [] anchors stack)
    choices used).trans sum

theorem Evaluates.finishes
    (evaluated : Evaluates module env expression heap value finalHeap (globals := globals))
    (choices : ChoiceSchedule) :
    ((evaluate (globals := globals) module env expression heap).run choices).Finishes
      ⟨.ok value, globals, finalHeap, heap.length⟩ := by
  obtain ⟨used, path⟩ := evaluated choices heap.length [] 0
  exact path.finishes (.done rfl)

/-- A returning block may mix ordinary heap operations and set traversal. -/
def BlockReturns (module : Module) (env : HeapCalls.Env) (body : List Stmt)
    (heap : Mutable.Heap) (value : Mutable.Value) (finalHeap : Mutable.Heap)
    (globals : Mutable.Globals := []) : Prop :=
  ∀ choices anchors stack used, ∃ finalUsed, Reaches choices module anchors
    ⟨⟨.block body env, stack, heap⟩, used⟩ ⟨⟨.value value, stack, finalHeap⟩, finalUsed⟩
    (globals := globals)

def ReturnsValue (module : Module) (name : String) (values : List Mutable.Value)
    (heap : Mutable.Heap) (value : Mutable.Value) (finalHeap : Mutable.Heap)
    (globals : Mutable.Globals := []) : Prop :=
  ∀ choices anchors stack used, ∃ finalUsed, Reaches choices module anchors
    ⟨⟨.operation (.call name) values, stack, heap⟩, used⟩
    ⟨⟨.value value, stack, finalHeap⟩, finalUsed⟩ (globals := globals)

theorem BlockReturns.of_heap
    (executed : HeapCalls.BlockReturns (globals := globals) module env body heap value finalHeap) :
    BlockReturns module env body heap value finalHeap (globals := globals) :=
  fun choices anchors stack used => ⟨used, Reaches.of_heap (executed anchors stack) choices used⟩

theorem BlockReturns.return_value
    (evaluated : Evaluates module env expression heap value finalHeap (globals := globals)) :
    BlockReturns module env (.return expression :: rest) heap value finalHeap (globals := globals) := by
  intro choices anchors stack used
  obtain ⟨finalUsed, path⟩ := evaluated choices anchors stack used
  exact ⟨finalUsed, .next rfl path⟩

theorem BlockReturns.after_heap
    (first : HeapCalls.BlockContinues (globals := globals) module env body heap middleEnv middleHeap)
    (rest : BlockReturns module middleEnv following middleHeap value finalHeap (globals := globals)) :
    BlockReturns module env (body ++ following) heap value finalHeap (globals := globals) := by
  intro choices anchors stack used
  obtain ⟨finalUsed, path⟩ := rest choices anchors stack used
  exact ⟨finalUsed, (Reaches.of_heap (first following anchors stack) choices used).trans path⟩

theorem BlockReturns.function (found : findFunctionIn module.body name = some (args, body))
    (arguments : completeArguments args values = some completed)
    (executed : BlockReturns module (functionEnv args body completed globals)
      (executableBody body) heap value finalHeap (globals := globals)) :
    ReturnsValue module name values heap value finalHeap (globals := globals) := by
  intro choices anchors stack used
  obtain ⟨finalUsed, path⟩ := executed choices anchors stack used
  exact ⟨finalUsed, .next (by simp [step, HeapCalls.step, found, arguments, liftStep]) path⟩

theorem ReturnsValue.of_heap
    (returned : HeapCalls.ReturnsValue (globals := globals) module name values heap value finalHeap) :
    ReturnsValue module name values heap value finalHeap (globals := globals) :=
  fun choices anchors stack used => ⟨used, Reaches.of_heap (returned anchors stack) choices used⟩

/-- Ordinary arguments keep their effects and do not consume iterator choices. -/
theorem Evaluates.call
    (arguments : HeapCalls.Evaluates.Arguments (globals := globals) module env expressions heap values middle)
    (callee : ReturnsValue module name values middle value finalHeap (globals := globals)) :
    Evaluates module env (.call (.name name) expressions) heap value finalHeap (globals := globals) := by
  intro choices anchors stack used
  obtain ⟨finalUsed, path⟩ := callee choices anchors stack used
  refine ⟨finalUsed, .next rfl ?_⟩
  exact (Reaches.of_heap
    (HeapCalls.Evaluates.arguments_reach arguments (.call name) [] anchors stack) choices used).trans path

theorem ReturnsValue.finishes
    (returned : ReturnsValue module name values heap value finalHeap (globals := globals))
    (choices : ChoiceSchedule) :
    ((call (globals := globals) module name values heap).run choices).Finishes
      ⟨.ok value, globals, finalHeap, heap.length⟩ := by
  obtain ⟨used, path⟩ := returned choices heap.length [] 0
  exact path.finishes (.done rfl)

/-- A pure generator body may map or filter each selected representative. The
invariant retains captured locals; the sum is independent of the schedule. -/
theorem sum_map_loop (choices : ChoiceSchedule) (module : Module)
    (heap : Mutable.Heap) (address : Nat) (original remaining : List Constant)
    (found : heap[address]? = some (.set original))
    (subset : ∀ item ∈ remaining, item ∈ original)
    (name : String) (body : List Stmt) (weight : Constant → Int)
    (invariant : HeapCalls.Env → Prop) (control : Calls.loopControl body = false)
    (iteration : ∀ env total item, invariant env → item ∈ original →
      env sumAccumulator = some (.scalar (.int total)) →
      ∃ updated, HeapCalls.BlockContinues (globals := globals) module
        (setLocal env name (.scalar item)) body heap updated heap ∧ invariant updated ∧
        updated sumAccumulator = some (.scalar (.int (total + weight item))))
    (total : Int) (env : HeapCalls.Env) (valid : invariant env)
    (accumulator : env sumAccumulator = some (.scalar (.int total)))
    (anchors : Nat) (stack : List HeapCalls.Frame) (used : Nat) :
    ∃ finalUsed, Reaches choices module anchors
      ⟨⟨.block [.setStepLoop name address original remaining body [],
        .return (.name sumAccumulator)] env, stack, heap⟩, used⟩
      ⟨⟨.value (.scalar (.int (total + (remaining.map weight).sum))), stack, heap⟩, finalUsed⟩
      (globals := globals) := by
  cases remainingEq : remaining with
  | nil =>
      refine ⟨used, .next (following :=
        ⟨⟨.block [.return (.name sumAccumulator)] env, stack, heap⟩, used⟩) ?_ ?_⟩
      · simp [step, HeapCalls.step, iteratorStep, found]
      · simpa using Reaches.of_heap
          ((HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup accumulator)) anchors stack)
          choices used
  | cons head tail =>
      simp only [remainingEq] at subset
      let index := choices used % (head :: tail).length
      have bound : index < (head :: tail).length := Nat.mod_lt _ (by simp)
      let item := (head :: tail)[index]
      have selected : (head :: tail)[choices used % (tail.length + 1)]? = some item :=
        List.getElem?_eq_getElem bound
      let rest := (head :: tail).eraseIdx index
      obtain ⟨updated, emitted, updatedValid, updatedTotal⟩ :=
        iteration env total item valid (subset item (List.getElem_mem bound)) accumulator
      obtain ⟨finalUsed, completed⟩ := sum_map_loop choices module heap address original rest found
        (fun value member => subset value (List.mem_of_mem_eraseIdx member))
        name body weight invariant control iteration (total + weight item) updated
        updatedValid updatedTotal anchors stack (used + 1)
      refine ⟨finalUsed, .next (following :=
        ⟨⟨.block (body ++ [.setStepLoop name address original rest body [],
            .return (.name sumAccumulator)]) (setLocal env name (.scalar item)), stack, heap⟩,
          used + 1⟩) ?_ ?_⟩
      · simp [step, HeapCalls.step, iteratorStep, found, selected, index,
          Calls.loopContinuation, control, rest]
      · have path := Reaches.of_heap
          (emitted [.setStepLoop name address original rest body [],
            .return (.name sumAccumulator)] anchors stack) choices (used + 1)
        have conservation := sum_eraseIdx weight (head :: tail) index bound
        have same : total + weight item + (rest.map weight).sum =
            total + ((head :: tail).map weight).sum :=
          (Int.add_assoc ..).trans (congrArg (fun n => total + n) conservation)
        rw [same] at completed
        exact path.trans completed
termination_by remaining.length
decreasing_by
  simp only [remainingEq]
  change ((head :: tail).eraseIdx index).length < (head :: tail).length
  rw [List.length_eraseIdx_of_lt bound]
  simp

/-- Acquire the first set iterator before evaluating the ordinary start argument.
The captured representatives remain the iterator's original state even if the
start expression mutates the set. Filters and later iterators execute lazily. -/
theorem Evaluates.sum_generator_set
    (ordinary : ∀ expressions, iterable ≠ .call (.name "range") expressions)
    (evaluated : HeapCalls.Evaluates (globals := globals) module env iterable heap (.ref address) middle)
    (found : middle[address]? = some (.set items))
    (started : HeapCalls.Evaluates (globals := globals) module env start middle initial afterStart)
    (accepted : sumInitial initial afterStart = some (.ok initial, afterStart))
    (executed : BlockReturns (globals := globals) module
      (setLocal (comprehensionEnv env ((name, iterable, filters) :: generators)) sumAccumulator initial)
      [.setStepLoop name address items items (comprehensionFilters filters (sumBody element generators)) [],
        .return (.name sumAccumulator)] afterStart answer finalHeap) :
    Evaluates (globals := globals) module env
      (.sumGenerator element ((name, iterable, filters) :: generators) start) heap answer finalHeap := by
  intro choices anchors stack used
  obtain ⟨finalUsed, loop⟩ := executed choices anchors (.generatorEnd :: stack) used
  have first : HeapCalls.step (globals := globals) module anchors
      ⟨.expr (.sumGenerator element ((name, iterable, filters) :: generators) start) env, stack, heap⟩ =
      .next (argumentsState (.sumGenerator element ((name, iterable, filters) :: generators) env start)
        env [] [iterable] stack heap) := by
    cases iterable <;> simp_all [HeapCalls.step]
  refine ⟨finalUsed, .next (following :=
    ⟨argumentsState (.sumGenerator element ((name, iterable, filters) :: generators) env start)
      env [] [iterable] stack heap, used⟩) (by simp [step, first, liftStep]) ?_⟩
  apply (Reaches.of_heap (HeapCalls.Evaluates.arguments_reach
    (.cons evaluated .nil) (.sumGenerator element ((name, iterable, filters) :: generators) env start)
    [] anchors stack) choices used).trans
  apply Reaches.next (following :=
    ⟨⟨.expr start env, .sumStart
      (.setStepLoop name address items items (comprehensionFilters filters (sumBody element generators)) [])
      (comprehensionEnv env ((name, iterable, filters) :: generators)) :: stack, middle⟩, used⟩)
  · cases iterable <;> simp_all [step, HeapCalls.step, sumGeneratorStart, run,
      Mutable.sequence, Mutable.unsupported, iteratorStep]
  apply (Reaches.of_heap (started anchors _) choices used).trans
  apply Reaches.next (following :=
    ⟨⟨.block [.setStepLoop name address items items
        (comprehensionFilters filters (sumBody element generators)) [], .return (.name sumAccumulator)]
      (setLocal (comprehensionEnv env ((name, iterable, filters) :: generators)) sumAccumulator initial),
      .generatorEnd :: stack, afterStart⟩, used⟩)
  · simp [step, HeapCalls.step, sumEnter, run, accepted, liftStep]
  exact loop.trans (.next rfl .refl)

end FormalSW.PyAst.SetCalls
