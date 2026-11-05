import lang.py.FormalSW.HeapRelocation
import lang.py.FormalSW.MembershipDispatchRelocation

/-! Relocation of suspended execution, including private loop cursors. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

def relocateSource (rename : Nat → Nat) : SequenceSource → SequenceSource
  | .scalar value => .scalar value
  | .ref address => .ref (rename address)

/-- Expressions contain no runtime references; internal statement cursors do. -/
def relocateStmt (rename : Nat → Nat) : Stmt → Stmt
  | .classDef name body => .classDef name (body.map (relocateStmt rename))
  | .functionDef name args returns body => .functionDef name args returns (body.map (relocateStmt rename))
  | .forIn target source body otherwise =>
      .forIn target source (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .forDictionaryItems target source body otherwise =>
      .forDictionaryItems target source (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .dictionaryItemsStepLoop name address keys position body otherwise =>
      .dictionaryItemsStepLoop name (rename address) (keys.map (relocateSource rename)) position
        (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .forZip target sources body otherwise =>
      .forZip target sources (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .forReversed name source body otherwise =>
      .forReversed name source (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .reverseSequenceStepLoop name source position body otherwise =>
      .reverseSequenceStepLoop name (relocateSource rename source) position
        (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .zipStepLoop name sources position body otherwise =>
      .zipStepLoop name (sources.map (relocateSource rename)) position
        (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .permutationStepLoop name rows body otherwise =>
      .permutationStepLoop name (rows.map (List.map (relocateSource rename)))
        (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .rangeLoop name position stop body otherwise =>
      .rangeLoop name position stop (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .rangeStepLoop name position stop stride body otherwise =>
      .rangeStepLoop name position stop stride (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .sequenceStepLoop name source position body otherwise =>
      .sequenceStepLoop name (relocateSource rename source) position
        (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .setStepLoop name address original remaining body otherwise =>
      .setStepLoop name (rename address) original remaining
        (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .keySetStepLoop name address originalSize remaining body otherwise =>
      .keySetStepLoop name (rename address) originalSize (remaining.map (relocateSource rename))
        (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .unpackStepLoop names source position body otherwise =>
      .unpackStepLoop names (relocateSource rename source) position
        (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .enumerateStepLoop index name source position counter body otherwise =>
      .enumerateStepLoop index name (relocateSource rename source) position counter
        (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .comprehensionAppend address element => .comprehensionAppend (rename address) element
  | .comprehensionAdd address element => .comprehensionAdd (rename address) element
  | .comprehensionStore address key value => .comprehensionStore (rename address) key value
  | .ifThen test yes no => .ifThen test (yes.map (relocateStmt rename)) (no.map (relocateStmt rename))
  | .whileDo test body otherwise => .whileDo test (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
  | .loopResume loop => .loopResume (relocateStmt rename loop)
  | statement => statement

/-- Extend bound-operation relocation to bodies containing internal loop state. -/
def relocateRuntimeOperation (rename : Nat → Nat) : Operation → Operation
  | .method receiver args body => .method (relocateValue rename receiver) args (body.map (relocateStmt rename))
  | .permutationStart target body otherwise following env =>
      .permutationStart target (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
        (following.map (relocateStmt rename)) (relocateEnv rename env)
  | .combinationStart target body otherwise following env =>
      .combinationStart target (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
        (following.map (relocateStmt rename)) (relocateEnv rename env)
  | .zipStart target body otherwise following env =>
      .zipStart target (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
        (following.map (relocateStmt rename)) (relocateEnv rename env)
  | operation => relocateOperation rename operation

def relocateSort (rename : Nat → Nat) (cursor : SequenceSort) : SequenceSort :=
  { cursor with env := relocateEnv rename cursor.env }

def relocateExtremum (rename : Nat → Nat) (cursor : SequenceExtremum) : SequenceExtremum :=
  { cursor with source := relocateValue rename cursor.source, env := relocateEnv rename cursor.env }

def relocatePair (rename : Nat → Nat) (pair : Value × Value) : Value × Value :=
  (relocateValue rename pair.1, relocateValue rename pair.2)

def relocateFrame (rename : Nat → Nat) : Frame → Frame
  | .sortedSource parameter key reverse env => .sortedSource parameter key reverse (relocateEnv rename env)
  | .sortedReverse source parameter key env =>
      .sortedReverse (relocateValue rename source) parameter key (relocateEnv rename env)
  | .sortedKey cursor candidate remaining keys =>
      .sortedKey (relocateSort rename cursor) (relocateValue rename candidate)
        (remaining.map (relocateValue rename)) (keys.map (relocatePair rename))
  | .extremumSource maximum parameter key env => .extremumSource maximum parameter key (relocateEnv rename env)
  | .extremumKey cursor position candidate best =>
      .extremumKey (relocateExtremum rename cursor) position (relocateValue rename candidate) (best.map (relocatePair rename))
  | .dictionaryItemsReceiver target body otherwise following env =>
      .dictionaryItemsReceiver target (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
        (following.map (relocateStmt rename)) (relocateEnv rename env)
  | .dictionaryValuesReceiver target body otherwise following env =>
      .dictionaryValuesReceiver target (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
        (following.map (relocateStmt rename)) (relocateEnv rename env)
  | .dictionaryKey value rest entries env =>
      .dictionaryKey value rest (entries.map fun entry => (entry.1, relocateValue rename entry.2)) (relocateEnv rename env)
  | .dictionaryValue key rest entries env =>
      .dictionaryValue key rest (entries.map fun entry => (entry.1, relocateValue rename entry.2)) (relocateEnv rename env)
  | .sumStart loop env => .sumStart (relocateStmt rename loop) (relocateEnv rename env)
  | .extremumStart hasDefault loop env => .extremumStart hasDefault (relocateStmt rename loop) (relocateEnv rename env)
  | .extremumResume original => .extremumResume (original.map (relocateFrame rename))
  | .generatorEnd => .generatorEnd
  | .generatorConsumer action => .generatorConsumer action
  | .generatorReceiver element generators env => .generatorReceiver element generators (relocateEnv rename env)
  | .initialized address => .initialized (rename address)
  | .attribute name => .attribute name
  | .methodReceiver name arguments env => .methodReceiver name arguments (relocateEnv rename env)
  | .assignAttribute base name rest env => .assignAttribute base name (rest.map (relocateStmt rename)) (relocateEnv rename env)
  | .augmentAttribute name op right rest env =>
      .augmentAttribute name op right (rest.map (relocateStmt rename)) (relocateEnv rename env)
  | .writeAttribute receiver name rest env =>
      .writeAttribute (relocateValue rename receiver) name (rest.map (relocateStmt rename)) (relocateEnv rename env)
  | .comprehensionResult address => .comprehensionResult (rename address)
  | .binaryLeft op right env inPlace => .binaryLeft op right (relocateEnv rename env) inPlace
  | .binaryRight op left inPlace => .binaryRight op (relocateValue rename left) inPlace
  | .compareLeft op right env => .compareLeft op right (relocateEnv rename env)
  | .compareRight op left => .compareRight op (relocateValue rename left)
  | .chainLeft op right rest env => .chainLeft op right rest (relocateEnv rename env)
  | .chainRight op left rest env => .chainRight op (relocateValue rename left) rest (relocateEnv rename env)
  | .chainResult right rest env => .chainResult (relocateValue rename right) rest (relocateEnv rename env)
  | .unary op => .unary op
  | .boolean op rest env => .boolean op rest (relocateEnv rename env)
  | .conditional yes no env => .conditional yes no (relocateEnv rename env)
  | .arguments operation done rest env =>
      .arguments (relocateRuntimeOperation rename operation) (done.map (relocateValue rename)) rest (relocateEnv rename env)
  | .starredArguments operation done rest env starred =>
      .starredArguments (relocateRuntimeOperation rename operation) (done.map (relocateValue rename)) rest
        (relocateEnv rename env) starred
  | .appendReceiver item env => .appendReceiver item (relocateEnv rename env)
  | .addReceiver item env => .addReceiver item (relocateEnv rename env)
  | .assign name rest env => .assign name (rest.map (relocateStmt rename)) (relocateEnv rename env)
  | .unpack names rest env => .unpack names (rest.map (relocateStmt rename)) (relocateEnv rename env)
  | .branch yes no rest env =>
      .branch (yes.map (relocateStmt rename)) (no.map (relocateStmt rename)) (rest.map (relocateStmt rename)) (relocateEnv rename env)
  | .discard rest env => .discard (rest.map (relocateStmt rename)) (relocateEnv rename env)
  | .assertion message rest env => .assertion message (rest.map (relocateStmt rename)) (relocateEnv rename env)
  | .assertionMessage => .assertionMessage
  | .reverseSequence name body otherwise following env =>
      .reverseSequence name (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
        (following.map (relocateStmt rename)) (relocateEnv rename env)
  | .sequence name body otherwise following env =>
      .sequence name (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
        (following.map (relocateStmt rename)) (relocateEnv rename env)
  | .unpackSequence names body otherwise following env =>
      .unpackSequence names (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
        (following.map (relocateStmt rename)) (relocateEnv rename env)
  | .enumerateSource index name start body otherwise following env =>
      .enumerateSource index name start (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
        (following.map (relocateStmt rename)) (relocateEnv rename env)
  | .enumerateStart index name source body otherwise following env =>
      .enumerateStart index name (relocateValue rename source) (body.map (relocateStmt rename)) (otherwise.map (relocateStmt rename))
        (following.map (relocateStmt rename)) (relocateEnv rename env)
  | .augmentItemReceiver index op right rest env =>
      .augmentItemReceiver index op right (rest.map (relocateStmt rename)) (relocateEnv rename env)
  | .augmentItemIndex receiver op right rest env =>
      .augmentItemIndex (relocateValue rename receiver) op right (rest.map (relocateStmt rename)) (relocateEnv rename env)
  | .writeItem receiver index rest env =>
      .writeItem (relocateValue rename receiver) (relocateValue rename index) (rest.map (relocateStmt rename)) (relocateEnv rename env)
  | .assignItem base index rest env => .assignItem base index (rest.map (relocateStmt rename)) (relocateEnv rename env)
  | .assignSlice base lower upper stride rest env =>
      .assignSlice base lower upper stride (rest.map (relocateStmt rename)) (relocateEnv rename env)
  | .rangeArguments name done rest body otherwise following env =>
      .rangeArguments name (done.map (relocateValue rename)) rest (body.map (relocateStmt rename))
        (otherwise.map (relocateStmt rename)) (following.map (relocateStmt rename)) (relocateEnv rename env)
  | .nextStart hasDefault loop env => .nextStart hasDefault (relocateStmt rename loop) (relocateEnv rename env)

def relocateWork (rename : Nat → Nat) : Work → Work
  | .sortedLoop cursor remaining keys =>
      .sortedLoop (relocateSort rename cursor) (remaining.map (relocateValue rename)) (keys.map (relocatePair rename))
  | .extremumLoop cursor position best =>
      .extremumLoop (relocateExtremum rename cursor) position (best.map (relocatePair rename))
  | .dictionary remaining entries env =>
      .dictionary remaining (entries.map fun entry => (entry.1, relocateValue rename entry.2)) (relocateEnv rename env)
  | .expr expression env => .expr expression (relocateEnv rename env)
  | .block body env => .block (body.map (relocateStmt rename)) (relocateEnv rename env)
  | .value value => .value (relocateValue rename value)
  | .operation operation values => .operation (relocateRuntimeOperation rename operation) (values.map (relocateValue rename))
  | .startRange name values body otherwise following env =>
      .startRange name (values.map (relocateValue rename)) (body.map (relocateStmt rename))
        (otherwise.map (relocateStmt rename)) (following.map (relocateStmt rename)) (relocateEnv rename env)

/-- The physical heap may also contain private cells, so it is supplied separately. -/
def relocateState (rename : Nat → Nat) (physical : Mutable.Heap) (state : State) : State :=
  ⟨relocateWork rename state.work, state.stack.map (relocateFrame rename), physical⟩

def relocateGlobals (rename : Nat → Nat) (globals : Mutable.Globals) : Mutable.Globals :=
  globals.map fun entry => (entry.1, relocateValue rename entry.2)

/-- Entry-root counts are not addresses and can differ between the two executions. -/
def relocateCompletion (rename : Nat → Nat) (physical : Mutable.Heap) (anchors : Nat)
    (completion : Mutable.Completion) : Mutable.Completion :=
  ⟨completion.outcome.map (relocateValue rename), relocateGlobals rename completion.globals, physical, anchors⟩

def relocateStep (rename : Nat → Nat) (physical : Mutable.Heap) (anchors : Nat) :
    Step State Mutable.Completion → Step State Mutable.Completion
  | .next state => .next (relocateState rename physical state)
  | .done outcome => .done (outcome.map (relocateCompletion rename physical anchors))
  | .unsupported => .unsupported

theorem relocateFrame_inGenerator (rename : Nat → Nat) (frame : Frame) :
    (relocateFrame rename frame).inGenerator = frame.inGenerator := by
  cases frame <;> simp only [relocateFrame, Frame.inGenerator]

theorem relocateStack_inGenerator (rename : Nat → Nat) (stack : List Frame) :
    (stack.map (relocateFrame rename)).any Frame.inGenerator = stack.any Frame.inGenerator := by
  simp [List.any_map, Function.comp_def, relocateFrame_inGenerator]

theorem protectGenerator_relocates (rename : Nat → Nat) (physical : Mutable.Heap) (anchors : Nat)
    (stack : List Frame) (transition : Step State Mutable.Completion) :
    protectGenerator (stack.map (relocateFrame rename)) (relocateStep rename physical anchors transition) =
      relocateStep rename physical anchors (protectGenerator stack transition) := by
  cases transition with
  | next | unsupported => rfl
  | done outcome =>
    cases outcome with
    | error error => rfl
    | ok completion =>
      rcases completion with ⟨outcome, globals, heap, entryCount⟩
      cases outcome <;>
        simp only [protectGenerator, relocateStep, relocateCompletion, Except.map, relocateStack_inGenerator]

/-- A completed primitive can be resumed under any relocated continuation stack. -/
theorem result_relocates (rename : Nat → Nat) (logical physical logicalAfter physicalAfter : Mutable.Heap)
    (logicalAnchors physicalAnchors : Nat) (action otherAction : Mutable.Eval Value)
    (stack : List Frame) (globals : Mutable.Globals) (outcome : Except ExceptionObject Value)
    (executed : action logical = some (outcome, logicalAfter))
    (other : otherAction physical = some (outcome.map (relocateValue rename), physicalAfter)) :
    result (globals := relocateGlobals rename globals) physicalAnchors physical otherAction
        (stack.map (relocateFrame rename)) =
      relocateStep rename physicalAfter physicalAnchors (result (globals := globals) logicalAnchors logical action stack) := by
  cases outcome <;>
    simp [result, run, executed, other, done, relocateStep, relocateState, relocateWork, relocateCompletion, Except.map]

theorem argumentsState_relocates (rename : Nat → Nat) (logical physical : Mutable.Heap)
    (operation : Operation) (env : Env) (done : List Value) (expressions : List Expr) (stack : List Frame) :
    argumentsState (relocateRuntimeOperation rename operation) (relocateEnv rename env)
        (done.map (relocateValue rename)) expressions (stack.map (relocateFrame rename)) physical =
      relocateState rename physical (argumentsState operation env done expressions stack logical) := by
  cases expressions <;> simp [argumentsState, relocateState, relocateWork, relocateFrame]

theorem step_compare_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (op : CmpOp) (left right : Value) (stack : List Frame) (globals : Mutable.Globals)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Mutable.Heap)
    (executed : HeapCalls.compare op left right logical = some (outcome, after)) :
    step module physicalAnchors (relocateState rename physical ⟨.value right, .compareRight op left :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value right, .compareRight op left :: stack, logical⟩ globals) := by
  have other := layout.compare op left right leftInside rightInside outcome after executed
  have transported := result_relocates rename logical physical after physical logicalAnchors physicalAnchors
    (HeapCalls.compare op left right) (HeapCalls.compare op (relocateValue rename left) (relocateValue rename right))
    stack globals outcome executed other.1
  simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step]
  rw [transported]
  simpa only [List.map_cons, relocateFrame] using
    protectGenerator_relocates rename physical physicalAnchors (.compareRight op left :: stack)
      (result (globals := globals) logicalAnchors logical (HeapCalls.compare op left right) stack)

theorem step_membership_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (needle container : Value) (negated : Bool) (stack : List Frame) (globals : Mutable.Globals)
    (needleInside : needle.edge.Within logical.length) (containerInside : container.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Mutable.Heap)
    (executed : HeapCalls.membership needle container negated logical = some (outcome, after)) :
    step module physicalAnchors
        (relocateState rename physical ⟨.operation (.membership negated) [needle, container], stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.operation (.membership negated) [needle, container], stack, logical⟩ globals) := by
  have other := layout.membership needle container negated needleInside containerInside outcome after executed
  have transported := result_relocates rename logical physical after physical logicalAnchors physicalAnchors
    (HeapCalls.membership needle container negated)
    (HeapCalls.membership (relocateValue rename needle) (relocateValue rename container) negated)
    stack globals outcome executed other.1
  simp only [relocateState, relocateWork, relocateRuntimeOperation, relocateOperation, List.map_cons, List.map_nil,
    step, primitive]
  rw [transported]
  exact protectGenerator_relocates rename physical physicalAnchors stack _

theorem step_assign_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (name : String) (rest : List Stmt) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors (relocateState rename physical ⟨.value value, .assign name rest env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .assign name rest env :: stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step, protectGenerator_next,
    relocateStep, relocateEnv_set]

theorem step_arguments_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (operation : Operation) (done : List Value)
    (rest : List Expr) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value value, .arguments operation done rest env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .arguments operation done rest env :: stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step, protectGenerator_next, relocateStep]
  rw [← List.map_singleton (f := relocateValue rename), ← List.map_append]
  exact congrArg Step.next (argumentsState_relocates rename logical physical operation env (done ++ [value]) rest stack)

theorem step_constant_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Constant) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors (relocateState rename physical ⟨.expr (.constant value) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.expr (.constant value) env, stack, logical⟩ globals) := rfl

theorem step_lookup_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (name : String) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors (relocateState rename physical ⟨.expr (.name name) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.expr (.name name) env, stack, logical⟩ globals) := by
  cases found : env name with
  | some value => simp [relocateState, relocateWork, step, relocateEnv, found, relocateStep]
  | none =>
    simp only [relocateState, relocateWork, step, relocateEnv, found, Option.map_none]
    rw [← protectGenerator_relocates]
    rfl

theorem step_membership_expression_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (needle container : Expr) (negated : Bool)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.expr (.membership needle container negated) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.expr (.membership needle container negated) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, step, protectGenerator_next, relocateStep]
  exact congrArg Step.next (argumentsState_relocates rename logical physical (.membership negated) env [] [needle, container] stack)

theorem step_compare_left_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (op : CmpOp) (right : Expr)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors (relocateState rename physical ⟨.value value, .compareLeft op right env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .compareLeft op right env :: stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step, protectGenerator_next, relocateStep]

theorem step_chain_compare_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (op : CmpOp) (left right : Value) (rest : List (CmpOp × Expr)) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Mutable.Heap)
    (executed : HeapCalls.compare op left right logical = some (outcome, after)) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value right, .chainRight op left rest env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value right, .chainRight op left rest env :: stack, logical⟩ globals) := by
  have other := layout.compare op left right leftInside rightInside outcome after executed
  have transported := result_relocates rename logical physical after physical logicalAnchors physicalAnchors
    (HeapCalls.compare op left right) (HeapCalls.compare op (relocateValue rename left) (relocateValue rename right))
    (.chainResult right rest env :: stack) globals outcome executed other.1
  simp only [List.map_cons, relocateFrame] at transported
  simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step]
  rw [transported]
  simpa only [List.map_cons, relocateFrame] using
    protectGenerator_relocates rename physical physicalAnchors (.chainRight op left rest env :: stack)
      (result (globals := globals) logicalAnchors logical (HeapCalls.compare op left right) (.chainResult right rest env :: stack))

end FormalSW.PyAst.HeapCalls.Relocation
