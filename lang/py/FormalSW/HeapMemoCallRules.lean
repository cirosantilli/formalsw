import lang.py.FormalSW.HeapMemoCalls

/-! Compositional rules for heap-valued memoization and source generator consumers. -/
namespace FormalSW.PyAst.HeapMemoCalls
variable {globals : Mutable.Globals}

/-- A source module has no way to enter the target's cached helpers. -/
def CacheDisjoint (target source : Module) : Prop :=
  ∀ name, name ∈ target.memoizedFunctions → findFunctionIn source.body name = none ∧
    libraryFunction source name = none ∧ source.findClass name = none

/-- Ordinary source runs preserve the same cache while allocating private objects. -/
theorem Reaches.from_heap (extension : HeapCalls.Extends target source)
    (disjoint : CacheDisjoint target source)
    (run : HeapCalls.Reaches (globals := globals) source anchors initial final) :
    Reaches (globals := globals) target anchors ⟨initial, callers, cache⟩ ⟨final, callers, cache⟩ := by
  induction run with
  | refl => exact .refl
  | @next current following final globals transition rest ih =>
      apply Reaches.next (following := ⟨following, callers, cache⟩) ?_ ih
      apply step_raw
      · rcases current with ⟨work, stack, heap⟩
        cases work <;> try trivial
        case value value =>
          cases stack with
          | nil => simp [HeapCalls.step, HeapCalls.done, HeapCalls.protectGenerator] at transition
          | cons frame frames => trivial
        case expr expression env =>
          cases found : pooledTupleParts expression with
          | none => exact found
          | some parts =>
              rcases parts with ⟨identity, items⟩
              have unsupported := pooled_unsupported (module := source) (anchors := anchors)
                (env := env) (stack := stack) (heap := heap) (globals := globals) found
              rw [unsupported] at transition
              contradiction
        case operation operation values =>
          cases operation <;> try trivial
          case call name =>
            intro cached
            obtain ⟨absent, library, classless⟩ := disjoint name cached
            simp [HeapCalls.step, absent, library, HeapCalls.construct, classless] at transition
      · rw [HeapCalls.step_extend extension _ (by simp [transition])]
        exact transition

theorem Runs.from_heap (extension : HeapCalls.Extends target source)
    (disjoint : CacheDisjoint target source)
    (run : HeapCalls.Reaches (globals := globals) source anchors initial final)
    (preserved : Cache.Preserves spec initial.heap final.heap) :
    Runs (globals := globals) target spec anchors initial final :=
  fun _callers cache valid => ⟨final, cache, rfl, preserved cache valid,
    Reaches.from_heap extension disjoint run⟩

theorem ReturnsValue.from_heap (extension : HeapCalls.Extends target source)
    (disjoint : CacheDisjoint target source)
    (run : HeapCalls.ReturnsValue (globals := globals) source name values heap value finalHeap)
    (preserved : Cache.Preserves spec heap finalHeap) :
    ReturnsValue (globals := globals) target spec name values heap value finalHeap :=
  fun anchors stack => Runs.from_heap extension disjoint (run anchors stack) preserved

theorem Evaluates.from_heap (extension : HeapCalls.Extends target source)
    (disjoint : CacheDisjoint target source)
    (run : HeapCalls.Evaluates (globals := globals) source env expression heap value finalHeap)
    (preserved : Cache.Preserves spec heap finalHeap) :
    Evaluates (globals := globals) target spec env expression heap value finalHeap :=
  fun anchors stack => Runs.from_heap extension disjoint (run anchors stack) preserved

namespace Evaluates

theorem constant : Evaluates (globals := globals) module spec env (.constant value) heap (.scalar value) heap :=
  fun _ _ => Runs.next (by first | exact True.intro | exact rfl) rfl .refl

theorem lookup (found : env name = some value) :
    Evaluates (globals := globals) module spec env (.name name) heap value heap :=
  fun _ _ => Runs.next (by first | exact True.intro | exact rfl) (by simp [HeapCalls.step, found]) .refl

theorem binary (left : Evaluates (globals := globals) module spec env a heap av middle)
    (right : Evaluates (globals := globals) module spec env b middle bv afterRight)
    (operation : Mutable.binary op av bv afterRight = some (.ok value, finalHeap))
    (preserved : Cache.Preserves spec afterRight finalHeap := by intro cache valid; exact valid) :
    Evaluates (globals := globals) module spec env (.binOp a op b) heap value finalHeap := by
  intro anchors stack
  exact Runs.next (by first | exact True.intro | exact rfl) rfl ((left _ _).trans (Runs.next (by first | exact True.intro | exact rfl) rfl ((right _ _).trans
    (Runs.next (by first | exact True.intro | exact rfl) (by simp [HeapCalls.step, HeapCalls.result, HeapCalls.run, operation]) .refl preserved))))

theorem compare (left : Evaluates (globals := globals) module spec env a heap av middle)
    (right : Evaluates (globals := globals) module spec env b middle bv afterRight)
    (operation : HeapCalls.compare op av bv afterRight = some (.ok value, finalHeap))
    (preserved : Cache.Preserves spec afterRight finalHeap := by intro cache valid; exact valid) :
    Evaluates (globals := globals) module spec env (.compare a [(op, b)]) heap value finalHeap := by
  intro anchors stack
  exact Runs.next (by first | exact True.intro | exact rfl) rfl ((left _ _).trans (Runs.next (by first | exact True.intro | exact rfl) rfl ((right _ _).trans
    (Runs.next (by first | exact True.intro | exact rfl) (by simp [HeapCalls.step, HeapCalls.result, HeapCalls.run, operation]) .refl preserved))))

inductive Arguments (module : Module) (spec : Specification) (env : Env) :
    List Expr → Heap → List Value → Heap → (globals : Mutable.Globals := []) → Prop where
  | nil {globals : Mutable.Globals} : Arguments (globals := globals) module spec env [] heap [] heap
  | cons {globals : Mutable.Globals} : Evaluates (globals := globals) module spec env expression heap value middle →
      Arguments (globals := globals) module spec env expressions middle values finalHeap →
      Arguments (globals := globals) module spec env (expression :: expressions) heap (value :: values) finalHeap

theorem arguments_reach (run : Arguments (globals := globals) module spec env expressions heap values finalHeap)
    (operation : HeapCalls.Operation) (done : List Value) (anchors : Nat) (stack : List HeapCalls.Frame) :
    Runs (globals := globals) module spec anchors (HeapCalls.argumentsState operation env done expressions stack heap)
      ⟨.operation operation (done ++ values), stack, finalHeap⟩ := by
  induction run generalizing done with
  | nil => simp [HeapCalls.argumentsState]; exact .refl
  | @cons expression heap value middle expressions values finalHeap globals head tail ih =>
      apply (head _ _).trans
      refine Runs.next (by first | exact True.intro | exact rfl) rfl ?_
      simpa [List.append_assoc] using ih (done ++ [value])

theorem call (arguments : Arguments (globals := globals) module spec env expressions heap values middle)
    (callee : ReturnsValue (globals := globals) module spec name values middle value finalHeap) :
    Evaluates (globals := globals) module spec env (.call (.name name) expressions) heap value finalHeap := by
  intro anchors stack
  exact Runs.next (by first | exact True.intro | exact rfl) rfl ((arguments_reach arguments (.call name) [] anchors stack).trans (callee anchors stack))

theorem builtin (arguments : Arguments (globals := globals) module spec env expressions heap values middle)
    (operation : HeapCalls.primitive (.builtin name) values middle = some (.ok value, finalHeap))
    (preserved : Cache.Preserves spec middle finalHeap := by intro cache valid; exact valid) :
    Evaluates (globals := globals) module spec env (.builtinCall name expressions) heap value finalHeap := by
  intro anchors stack
  have next : HeapCalls.step module anchors
      ⟨.operation (.builtin name) values, stack, middle⟩ globals =
      .next ⟨.value value, stack, finalHeap⟩ := by
    cases name with
    | all | any => simp [HeapCalls.primitive, Mutable.unsupported] at operation
    | _ => simp [HeapCalls.step, HeapCalls.result, HeapCalls.run, operation]
  exact Runs.next (by first | exact True.intro | exact rfl) rfl ((arguments_reach arguments (.builtin name) [] anchors stack).trans
    (Runs.next (by first | exact True.intro | exact rfl) next .refl preserved))

theorem tuple (arguments : Arguments (globals := globals) module spec env expressions heap values after)
    (preserved : Cache.Preserves spec after (after ++ [.tuple values]))
    (nonempty : values ≠ [] := by simp) :
    Evaluates (globals := globals) module spec env (.tuple expressions) heap (.ref after.length)
      (after ++ [.tuple values]) := by
  intro anchors stack
  apply Runs.next (current := ⟨.expr (.tuple expressions) env, stack, heap⟩)
    (following := HeapCalls.argumentsState .tuple env [] expressions stack heap) (by first | exact True.intro | exact rfl) rfl
  apply (arguments_reach arguments .tuple [] anchors stack).trans
  have notEmpty : values.isEmpty = false := by cases values <;> simp_all
  exact Runs.next (by first | exact True.intro | exact rfl) (by simp [HeapCalls.step, HeapCalls.result, HeapCalls.run,
    HeapCalls.primitive, Mutable.allocateTuple, notEmpty, Except.map]) .refl preserved

theorem subscript (base : Evaluates (globals := globals) module spec env a heap av middle)
    (index : Evaluates (globals := globals) module spec env b middle bv afterIndex)
    (operation : Mutable.getItem av bv afterIndex = some (.ok value, finalHeap))
    (preserved : Cache.Preserves spec afterIndex finalHeap := by intro cache valid; exact valid)
    (ordinary : ∀ x y z, b ≠ .slice x y z := by intros; contradiction) :
    Evaluates (globals := globals) module spec env (.subscript a b) heap value finalHeap := by
  intro anchors stack
  apply Runs.next (current := ⟨.expr (.subscript a b) env, stack, heap⟩)
    (following := HeapCalls.argumentsState .subscript env [] [a, b] stack heap) (by first | exact True.intro | exact rfl)
  · cases b <;> simp_all [HeapCalls.step]
  apply (arguments_reach (.cons base (.cons index .nil)) .subscript [] anchors stack).trans
  exact Runs.next (by first | exact True.intro | exact rfl) (by simp [HeapCalls.step, HeapCalls.result, HeapCalls.run,
    HeapCalls.primitive, operation]) .refl preserved

end Evaluates

namespace BlockReturns

theorem return_value (evaluated : Evaluates (globals := globals) module spec env expression heap value finalHeap) :
    BlockReturns (globals := globals) module spec env (.return expression :: rest) heap value finalHeap :=
  fun anchors stack => Runs.next (by first | exact True.intro | exact rfl) rfl (evaluated anchors stack)

theorem assign (evaluated : Evaluates (globals := globals) module spec env expression heap value middle)
    (rest : BlockReturns (globals := globals) module spec (HeapCalls.setLocal env name value) body middle answer finalHeap) :
    BlockReturns (globals := globals) module spec env (.assign [.name name] expression :: body) heap answer finalHeap :=
  fun anchors stack => Runs.next (by first | exact True.intro | exact rfl) rfl ((evaluated anchors _).trans (Runs.next (by first | exact True.intro | exact rfl) rfl (rest anchors stack)))

theorem branch (evaluated : Evaluates (globals := globals) module spec env condition heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockReturns (globals := globals) module spec env ((if flag then yes else no) ++ body) middle answer finalHeap) :
    BlockReturns (globals := globals) module spec env (.ifThen condition yes no :: body) heap answer finalHeap := by
  intro anchors stack
  exact Runs.next (by first | exact True.intro | exact rfl) rfl ((evaluated anchors _).trans
    (Runs.next (by first | exact True.intro | exact rfl) (by simp [HeapCalls.step, HeapCalls.run, truth]) (rest anchors stack)))

theorem function (plain : name ∉ module.memoizedFunctions)
    (found : findFunctionIn module.body name = some (args, body))
    (arguments : HeapCalls.completeArguments args values = some completed)
    (evaluated : BlockReturns (globals := globals) module spec
      (HeapCalls.functionEnv args body completed globals) (executableBody body) heap value finalHeap) :
    ReturnsValue (globals := globals) module spec name values heap value finalHeap := by
  intro anchors stack
  exact Runs.next plain (by simp [HeapCalls.step, found, arguments]) (evaluated anchors stack)

end BlockReturns

/-- Relational argument evaluation follows source order and shares the cache. -/
def ArgumentsRel (module : Module) (spec : Specification) (env : Env) (expressions : List Expr)
    (heap : Heap) (post : List Value → Heap → Prop) (globals : Mutable.Globals := []) : Prop :=
  ∀ operation done anchors stack, RunsRel (globals := globals) module spec anchors
    (HeapCalls.argumentsState operation env done expressions stack heap)
    (fun final => ∃ values after,
      final = ⟨.operation operation (done ++ values), stack, after⟩ ∧ post values after)

namespace ArgumentsRel

theorem nil (holds : post [] heap) : ArgumentsRel (globals := globals) module spec env [] heap post := by
  intro operation done anchors stack
  exact RunsRel.refl ⟨[], heap, by simp [HeapCalls.argumentsState], holds⟩

theorem cons (head : EvaluatesRel (globals := globals) module spec env expression heap headPost)
    (tail : ∀ value middle, headPost value middle →
      ArgumentsRel (globals := globals) module spec env expressions middle (fun values after => post (value :: values) after)) :
    ArgumentsRel (globals := globals) module spec env (expression :: expressions) heap post := by
  intro operation done anchors stack
  apply (head anchors (.arguments operation done expressions env :: stack)).bind
  rintro state ⟨value, middle, rfl, holds⟩
  apply RunsRel.next (current := ⟨.value value, .arguments operation done expressions env :: stack, middle⟩) (by first | exact True.intro | exact rfl) rfl
  apply (tail value middle holds operation (done ++ [value]) anchors stack).consequence
  rintro final ⟨values, after, rfl, holds⟩
  exact ⟨value :: values, after, by simp [List.append_assoc], holds⟩

theorem fixed (arguments : Evaluates.Arguments (globals := globals) module spec env expressions heap values after) :
    ArgumentsRel (globals := globals) module spec env expressions heap
      (fun actual final => actual = values ∧ final = after) := by
  intro operation done anchors stack
  apply (Evaluates.arguments_reach arguments operation done anchors stack).consequence
  rintro final rfl
  exact ⟨values, after, rfl, rfl, rfl⟩

end ArgumentsRel

namespace EvaluatesRel

theorem constant (holds : post (.scalar value) heap) :
    EvaluatesRel (globals := globals) module spec env (.constant value) heap post :=
  Evaluates.constant.rel.consequence (by rintro _ _ ⟨rfl, rfl⟩; exact holds)

theorem lookup (found : env name = some value) (holds : post value heap) :
    EvaluatesRel (globals := globals) module spec env (.name name) heap post :=
  (Evaluates.lookup found).rel.consequence (by rintro _ _ ⟨rfl, rfl⟩; exact holds)

theorem call (arguments : ArgumentsRel (globals := globals) module spec env expressions heap argumentPost)
    (callee : ∀ values middle, argumentPost values middle → ReturnsRel (globals := globals) module spec name values middle post) :
    EvaluatesRel (globals := globals) module spec env (.call (.name name) expressions) heap post := by
  intro anchors stack
  apply RunsRel.next (current := ⟨.expr (.call (.name name) expressions) env, stack, heap⟩) (by first | exact True.intro | exact rfl) rfl
  apply (arguments (.call name) [] anchors stack).bind
  rintro final ⟨values, middle, rfl, holds⟩
  exact callee values middle holds anchors stack

theorem tuple (arguments : ArgumentsRel (globals := globals) module spec env expressions heap argumentPost)
    (selected : ∀ values after, argumentPost values after →
      values ≠ [] ∧ Cache.Preserves spec after (after ++ [.tuple values]) ∧ post (.ref after.length) (after ++ [.tuple values])) :
    EvaluatesRel (globals := globals) module spec env (.tuple expressions) heap post := by
  intro anchors stack
  apply RunsRel.next (current := ⟨.expr (.tuple expressions) env, stack, heap⟩)
    (following := HeapCalls.argumentsState .tuple env [] expressions stack heap) (by first | exact True.intro | exact rfl) rfl
  apply (arguments .tuple [] anchors stack).bind
  rintro final ⟨values, after, rfl, holds⟩
  obtain ⟨nonempty, preserved, holds⟩ := selected values after holds
  have notEmpty : values.isEmpty = false := by cases values <;> simp_all
  exact RunsRel.next (by first | exact True.intro | exact rfl) (by simp [HeapCalls.step, HeapCalls.result, HeapCalls.run,
    HeapCalls.primitive, Mutable.allocateTuple, notEmpty, Except.map])
    (RunsRel.refl ⟨.ref after.length, after ++ [.tuple values], rfl, holds⟩) preserved

theorem builtin (arguments : ArgumentsRel (globals := globals) module spec env expressions heap argumentPost)
    (selected : ∀ values middle, argumentPost values middle → ∃ value after,
      HeapCalls.primitive (.builtin name) values middle = some (.ok value, after) ∧
      Cache.Preserves spec middle after ∧ post value after) :
    EvaluatesRel (globals := globals) module spec env (.builtinCall name expressions) heap post := by
  intro anchors stack
  apply RunsRel.next (current := ⟨.expr (.builtinCall name expressions) env, stack, heap⟩) (by first | exact True.intro | exact rfl) rfl
  apply (arguments (.builtin name) [] anchors stack).bind
  rintro final ⟨values, middle, rfl, holds⟩
  obtain ⟨value, after, operation, preserved, holds⟩ := selected values middle holds
  have next : HeapCalls.step module anchors
      ⟨.operation (.builtin name) values, stack, middle⟩ globals = .next ⟨.value value, stack, after⟩ := by
    cases name with
    | all | any => simp [HeapCalls.primitive, Mutable.unsupported] at operation
    | _ => simp [HeapCalls.step, HeapCalls.result, HeapCalls.run, operation]
  exact RunsRel.next (by first | exact True.intro | exact rfl) next (RunsRel.refl ⟨value, after, rfl, holds⟩) preserved

theorem binary {rightPost : Value → Heap → Value → Heap → Prop}
    (left : EvaluatesRel (globals := globals) module spec env a heap leftPost)
    (right : ∀ av middle, leftPost av middle → EvaluatesRel (globals := globals) module spec env b middle (rightPost av middle))
    (selected : ∀ av middle bv afterRight, leftPost av middle → rightPost av middle bv afterRight →
      ∃ value after, Mutable.binary op av bv afterRight = some (.ok value, after) ∧
        Cache.Preserves spec afterRight after ∧ post value after) :
    EvaluatesRel (globals := globals) module spec env (.binOp a op b) heap post := by
  intro anchors stack
  apply RunsRel.next (current := ⟨.expr (.binOp a op b) env, stack, heap⟩) (by first | exact True.intro | exact rfl) rfl
  apply (left anchors (.binaryLeft op b env false :: stack)).bind
  rintro final ⟨av, middle, rfl, leftHolds⟩
  apply RunsRel.next (current := ⟨.value av, .binaryLeft op b env false :: stack, middle⟩) (by first | exact True.intro | exact rfl) rfl
  apply (right av middle leftHolds anchors (.binaryRight op av false :: stack)).bind
  rintro final ⟨bv, afterRight, rfl, rightHolds⟩
  obtain ⟨value, after, operation, preserved, holds⟩ := selected av middle bv afterRight leftHolds rightHolds
  exact RunsRel.next (by first | exact True.intro | exact rfl) (by simp [HeapCalls.step, HeapCalls.result, HeapCalls.run, operation])
    (RunsRel.refl ⟨value, after, rfl, holds⟩) preserved

theorem compare {rightPost : Value → Heap → Value → Heap → Prop}
    (left : EvaluatesRel (globals := globals) module spec env a heap leftPost)
    (right : ∀ av middle, leftPost av middle → EvaluatesRel (globals := globals) module spec env b middle (rightPost av middle))
    (selected : ∀ av middle bv afterRight, leftPost av middle → rightPost av middle bv afterRight →
      ∃ value after, HeapCalls.compare op av bv afterRight = some (.ok value, after) ∧
        Cache.Preserves spec afterRight after ∧ post value after) :
    EvaluatesRel (globals := globals) module spec env (.compare a [(op, b)]) heap post := by
  intro anchors stack
  apply RunsRel.next (current := ⟨.expr (.compare a [(op, b)]) env, stack, heap⟩) (by first | exact True.intro | exact rfl) rfl
  apply (left anchors (.compareLeft op b env :: stack)).bind
  rintro final ⟨av, middle, rfl, leftHolds⟩
  apply RunsRel.next (current := ⟨.value av, .compareLeft op b env :: stack, middle⟩) (by first | exact True.intro | exact rfl) rfl
  apply (right av middle leftHolds anchors (.compareRight op av :: stack)).bind
  rintro final ⟨bv, afterRight, rfl, rightHolds⟩
  obtain ⟨value, after, operation, preserved, holds⟩ := selected av middle bv afterRight leftHolds rightHolds
  exact RunsRel.next (by first | exact True.intro | exact rfl) (by simp [HeapCalls.step, HeapCalls.result, HeapCalls.run, operation])
    (RunsRel.refl ⟨value, after, rfl, holds⟩) preserved

theorem subscript {indexPost : Value → Heap → Value → Heap → Prop}
    (base : EvaluatesRel (globals := globals) module spec env a heap basePost)
    (index : ∀ av middle, basePost av middle → EvaluatesRel (globals := globals) module spec env b middle (indexPost av middle))
    (selected : ∀ av middle bv afterIndex, basePost av middle → indexPost av middle bv afterIndex →
      ∃ value after, Mutable.getItem av bv afterIndex = some (.ok value, after) ∧
        Cache.Preserves spec afterIndex after ∧ post value after)
    (ordinary : ∀ x y z, b ≠ .slice x y z := by intros; contradiction) :
    EvaluatesRel (globals := globals) module spec env (.subscript a b) heap post := by
  intro anchors stack
  apply RunsRel.next (current := ⟨.expr (.subscript a b) env, stack, heap⟩)
    (following := HeapCalls.argumentsState .subscript env [] [a, b] stack heap) (by first | exact True.intro | exact rfl)
  · cases b <;> simp_all [HeapCalls.step]
  have arguments : ArgumentsRel (globals := globals) module spec env [a, b] heap
      (fun values after => ∃ av middle bv,
        values = [av, bv] ∧ basePost av middle ∧ indexPost av middle bv after) :=
    ArgumentsRel.cons base (fun av middle leftHolds =>
      ArgumentsRel.cons (index av middle leftHolds) (fun bv after rightHolds =>
        ArgumentsRel.nil ⟨av, middle, bv, rfl, leftHolds, rightHolds⟩))
  apply (arguments .subscript [] anchors stack).bind
  rintro final ⟨values, afterIndex, rfl, av, middle, bv, rfl, leftHolds, rightHolds⟩
  obtain ⟨value, after, operation, preserved, holds⟩ := selected av middle bv afterIndex leftHolds rightHolds
  exact RunsRel.next (by first | exact True.intro | exact rfl) (by simp [HeapCalls.step, HeapCalls.result, HeapCalls.run,
    HeapCalls.primitive, operation]) (RunsRel.refl ⟨value, after, rfl, holds⟩) preserved

end EvaluatesRel

namespace BlockReturnsRel

theorem return_value (evaluated : EvaluatesRel (globals := globals) module spec env expression heap post) :
    BlockReturnsRel (globals := globals) module spec env (.return expression :: rest) heap post :=
  fun anchors stack => RunsRel.next (by first | exact True.intro | exact rfl) rfl (evaluated anchors stack)

theorem assign (evaluated : EvaluatesRel (globals := globals) module spec env expression heap expressionPost)
    (rest : ∀ value middle, expressionPost value middle →
      BlockReturnsRel (globals := globals) module spec (HeapCalls.setLocal env name value) body middle post) :
    BlockReturnsRel (globals := globals) module spec env (.assign [.name name] expression :: body) heap post := by
  intro anchors stack
  apply RunsRel.next (current := ⟨.block (.assign [.name name] expression :: body) env, stack, heap⟩) (by first | exact True.intro | exact rfl) rfl
  apply (evaluated anchors (.assign name body env :: stack)).bind
  rintro final ⟨value, middle, rfl, holds⟩
  exact RunsRel.next (by first | exact True.intro | exact rfl) rfl (rest value middle holds anchors stack)

theorem branch (evaluated : EvaluatesRel (globals := globals) module spec env condition heap expressionPost)
    (rest : ∀ value middle, expressionPost value middle → ∃ flag,
      Mutable.truth value middle = some (.ok flag, middle) ∧
      BlockReturnsRel (globals := globals) module spec env ((if flag then yes else no) ++ body) middle post) :
    BlockReturnsRel (globals := globals) module spec env (.ifThen condition yes no :: body) heap post := by
  intro anchors stack
  apply RunsRel.next (current := ⟨.block (.ifThen condition yes no :: body) env, stack, heap⟩) (by first | exact True.intro | exact rfl) rfl
  apply (evaluated anchors (.branch yes no body env :: stack)).bind
  rintro final ⟨value, middle, rfl, holds⟩
  obtain ⟨flag, truth, continued⟩ := rest value middle holds
  exact RunsRel.next (by first | exact True.intro | exact rfl) (by simp [HeapCalls.step, HeapCalls.run, truth]) (continued anchors stack)

theorem function (plain : name ∉ module.memoizedFunctions)
    (found : findFunctionIn module.body name = some (args, body))
    (arguments : HeapCalls.completeArguments args values = some completed)
    (evaluated : BlockReturnsRel (globals := globals) module spec
      (HeapCalls.functionEnv args body completed globals) (executableBody body) heap post) :
    ReturnsRel (globals := globals) module spec name values heap post := by
  intro anchors stack
  exact RunsRel.next plain (by simp [HeapCalls.step, found, arguments]) (evaluated anchors stack)

theorem range_step (continues : Calls.rangeContinues next stop stride = true)
    (rest : BlockReturnsRel (globals := globals) module spec (HeapCalls.setLocal env name (.scalar (.int next)))
      (body ++ [Calls.loopContinuation body (.rangeStepLoop name (next + stride) stop stride body otherwise)] ++ following)
      heap post) :
    BlockReturnsRel (globals := globals) module spec env (.rangeStepLoop name next stop stride body otherwise :: following) heap post := by
  intro anchors stack
  exact RunsRel.next (by first | exact True.intro | exact rfl) (by simp [HeapCalls.step, continues]) (rest anchors stack)

theorem range_done (finished : Calls.rangeContinues next stop stride = false)
    (rest : BlockReturnsRel (globals := globals) module spec env (otherwise ++ following) heap post) :
    BlockReturnsRel (globals := globals) module spec env (.rangeStepLoop name next stop stride body otherwise :: following) heap post := by
  intro anchors stack
  exact RunsRel.next (by first | exact True.intro | exact rfl) (by simp [HeapCalls.step, finished]) (rest anchors stack)

end BlockReturnsRel

/-- Only the body of the consumed generator runs inside its generator boundary. -/
theorem EvaluatesRel.sum_generator_range
    (arguments : Evaluates.Arguments (globals := globals) module spec env expressions heap values middle)
    (bounds : HeapCalls.rangeBounds values = .ok (first, stop, stride))
    (started : Evaluates (globals := globals) module spec env start middle initial afterStart)
    (accepted : HeapCalls.sumInitial initial afterStart = some (.ok initial, afterStart))
    (executed : BlockReturnsRel (globals := globals) module spec
      (HeapCalls.setLocal (HeapCalls.comprehensionEnv env ((name, .call (.name "range") expressions, filters) :: generators))
        HeapCalls.sumAccumulator initial)
      [.rangeStepLoop name first stop stride (HeapCalls.comprehensionFilters filters (HeapCalls.sumBody element generators)) [],
        .return (.name HeapCalls.sumAccumulator)] afterStart post) :
    EvaluatesRel (globals := globals) module spec env
      (.sumGenerator element ((name, .call (.name "range") expressions, filters) :: generators) start) heap post := by
  intro anchors stack
  apply RunsRel.next (current := ⟨.expr
    (.sumGenerator element ((name, .call (.name "range") expressions, filters) :: generators) start) env, stack, heap⟩) (by first | exact True.intro | exact rfl) rfl
  apply (Evaluates.arguments_reach arguments _ [] anchors stack).bind
  rintro final rfl
  apply RunsRel.next (current := ⟨.operation
    (.sumGenerator element ((name, .call (.name "range") expressions, filters) :: generators) env start)
    values, stack, middle⟩) (following := ⟨.expr start env,
    .sumStart (.rangeStepLoop name first stop stride
      (HeapCalls.comprehensionFilters filters (HeapCalls.sumBody element generators)) [])
      (HeapCalls.comprehensionEnv env ((name, .call (.name "range") expressions, filters) :: generators)) :: stack,
    middle⟩) trivial (by simp [HeapCalls.step, HeapCalls.sumGeneratorStart, bounds])
  apply (started anchors _).bind
  rintro final rfl
  apply RunsRel.next (current := ⟨.value initial,
    .sumStart (.rangeStepLoop name first stop stride
      (HeapCalls.comprehensionFilters filters (HeapCalls.sumBody element generators)) [])
      (HeapCalls.comprehensionEnv env ((name, .call (.name "range") expressions, filters) :: generators)) :: stack,
    afterStart⟩) (following := ⟨.block
      [.rangeStepLoop name first stop stride (HeapCalls.comprehensionFilters filters (HeapCalls.sumBody element generators)) [],
        .return (.name HeapCalls.sumAccumulator)]
      (HeapCalls.setLocal (HeapCalls.comprehensionEnv env ((name, .call (.name "range") expressions, filters) :: generators))
        HeapCalls.sumAccumulator initial), .generatorEnd :: stack, afterStart⟩)
    trivial (by simp [HeapCalls.step, HeapCalls.sumEnter, HeapCalls.run, accepted])
  apply (executed anchors (.generatorEnd :: stack)).bind
  rintro final ⟨value, after, rfl, holds⟩
  exact RunsRel.next (by first | exact True.intro | exact rfl) rfl (RunsRel.refl ⟨value, after, rfl, holds⟩)

/-- The legacy optimized range-sum AST retains the same cache-aware generator execution. -/
theorem EvaluatesRel.sum_range
    (evaluated : EvaluatesRel (globals := globals) module spec env
      (.sumGenerator element [(name, .call (.name "range") bounds, filters)] (.constant (.int 0))) heap post) :
    EvaluatesRel (globals := globals) module spec env (.sumRange name element bounds filters) heap post :=
  fun anchors stack => RunsRel.next (by first | exact True.intro | exact rfl) rfl (evaluated anchors stack)

end FormalSW.PyAst.HeapMemoCalls
