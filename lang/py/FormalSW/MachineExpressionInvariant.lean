import lang.py.FormalSW.MachineLoopInvariant

/-! Expression invariants retain operand effects and all modeled primitive outcomes. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- A read-only primitive may succeed, raise, or remain unsupported. -/
theorem result_readonly_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (action otherAction : Mutable.Eval Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals)
    (effect : ∀ outcome after, action logical = some (outcome, after) →
      after = logical ∧ ∀ value, outcome = .ok value → value.edge.Within logical.length)
    (paired : otherAction physical =
      (action logical).map (fun pair => (pair.1.map (relocateValue rename), physical))) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical action stack globals)
      (result physicalAnchors physical otherAction (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  cases executed : action logical with
  | none =>
    apply Preserves.unchanged layout <;>
      simp [result, run, paired, executed, StepHeap, StepWithin, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    obtain ⟨same, bounded⟩ := effect outcome after executed
    subst after
    exact result_preserves logical physical logical physical rename rename logicalAnchors physicalAnchors
      action otherAction stack globals outcome (fun _ _ => rfl) (Nat.le_refl _) (Nat.le_refl _) layout
      stackInside globalsInside bounded executed (by simpa only [executed, Option.map_some] using paired)

theorem result_scalar_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (outcome : Option (Except ExceptionObject Constant))
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (scalarResult outcome) stack globals)
      (result physicalAnchors physical (scalarResult outcome) (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  apply result_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ stack globals layout stackInside globalsInside
  · intro result after executed
    obtain ⟨same, scalar⟩ := scalarResult_effect logical after outcome result executed
    refine ⟨same, ?_⟩
    intro value success
    obtain ⟨constant, rfl⟩ := scalar value success
    trivial
  · exact scalarResult_relocates logical physical rename outcome

theorem step_unary_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (op : UnaryOp) (value : Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .unary op :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .unary op :: stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value value, .unary op :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame :=
    fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)
  have raw := result_readonly_preserves logical physical rename logicalAnchors physicalAnchors
    (unary op value) (unary op (relocateValue rename value)) stack globals layout stackInside globalsInside (by
      intro outcome after executed
      obtain ⟨same, scalar⟩ := unary_effect logical after op value inside.1 outcome executed
      refine ⟨same, ?_⟩
      intro returned success
      obtain ⟨constant, rfl⟩ := scalar returned success
      trivial) (unary_relocates logical physical rename layout.runtime op value inside.1)
  simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame] using
    raw.protectGenerator (.unary op :: stack) inside.2

theorem step_binary_scalars_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (op : BinOp) (left right : Constant) (inPlace : Bool)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value (.scalar right), .binaryRight op (.scalar left) inPlace :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value (.scalar right), .binaryRight op (.scalar left) inPlace :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have full : ∀ frame ∈ .binaryRight op (.scalar left) inPlace :: stack, FrameWithin logical.length frame := by
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simp [FrameWithin, Mutable.Value.edge, Graph.Edge.Within]
    · exact stackInside frame member
  have raw := (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
    (scalarBinary op left right) stack globals layout stackInside globalsInside).protectGenerator
    (.binaryRight op (.scalar left) inPlace :: stack) full
  cases inPlace <;>
    simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame, relocateValue,
      Bool.false_eq_true, if_false, if_true, inplace, binary_scalars] using raw

theorem step_binaryLeft_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (op : BinOp) (right : Expr) (env : Env)
    (inPlace : Bool) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .binaryLeft op right env inPlace :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .binaryLeft op right env inPlace :: stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value value, .binaryLeft op right env inPlace :: stack, logical⟩)
        (relocateGlobals rename globals)) :=
  Preserves.unchanged layout rfl (StateWithin.binaryLeft logical value op right env inPlace stack inside)
    (step_binaryLeft_relocates module logical physical rename logicalAnchors physicalAnchors value op right env inPlace stack globals)

theorem step_binary_expression_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (left right : Expr) (op : BinOp) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.binOp left op right) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.binOp left op right) env, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.expr (.binOp left op right) env, stack, logical⟩)
        (relocateGlobals rename globals)) :=
  Preserves.unchanged layout rfl (StateWithin.binary_expression logical left right op env stack inside)
    (step_binary_expression_relocates module logical physical rename logicalAnchors physicalAnchors left right op env stack globals)

theorem step_unary_expression_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (op : UnaryOp) (operand : Expr) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.unaryOp op operand) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.unaryOp op operand) env, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.expr (.unaryOp op operand) env, stack, logical⟩)
        (relocateGlobals rename globals)) :=
  Preserves.unchanged layout rfl (StateWithin.unary_expression logical op operand env stack inside)
    (step_unary_expression_relocates module logical physical rename logicalAnchors physicalAnchors op operand env stack globals)

theorem step_chainResult_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value right : Value) (rest : List (CmpOp × Expr)) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .chainResult right rest env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .chainResult right rest env :: stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value value, .chainResult right rest env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · obtain ⟨truth, tested⟩ := truth_total logical value inside.1
    cases rest with
    | nil => rfl
    | cons next rest => cases next; cases truth <;> simp [step, run, tested, StepHeap]
  · exact StateWithin.chainResult module logical logicalAnchors value right rest env stack globals inside
  · exact step_chainResult_relocates module logical physical rename layout.runtime logicalAnchors physicalAnchors value right rest env stack globals inside.1

/-- Identity results are scalar, including the intentionally unsupported scalar-pooling cases. -/
theorem identity_scalar_result (left right : Value) :
    ∃ outcome : Option (Except ExceptionObject Constant), identity left right = scalarResult outcome := by
  cases left with
  | scalar left =>
    cases right with
    | scalar right => exact ⟨(scalarIdentity left right).map (fun value => .ok (.bool value)), rfl⟩
    | ref right => exact ⟨some (.ok (.bool false)), rfl⟩
  | ref left =>
    cases right with
    | scalar right => exact ⟨some (.ok (.bool false)), rfl⟩
    | ref right => exact ⟨some (.ok (.bool (left == right))), rfl⟩

theorem identity_relocates_value (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (left right : Value)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length) :
    identity (relocateValue rename left) (relocateValue rename right) physical =
      (identity left right logical).map (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  rw [identity_relocates layout left right leftInside rightInside]
  obtain ⟨outcome, equation⟩ := identity_scalar_result left right
  rw [equation]
  cases outcome with
  | none => rfl
  | some outcome => cases outcome <;> rfl

theorem step_identity_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (left right : Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.builtin .identity) [left, right], stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.builtin .identity) [left, right], stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have raw := result_readonly_preserves logical physical rename logicalAnchors physicalAnchors
    (identity left right) (identity (relocateValue rename left) (relocateValue rename right))
    stack globals layout stackInside globalsInside (by
      intro outcome after executed
      obtain ⟨result, equation⟩ := identity_scalar_result left right
      rw [equation] at executed
      obtain ⟨same, scalar⟩ := scalarResult_effect logical after result outcome executed
      refine ⟨same, ?_⟩
      intro returned success
      obtain ⟨constant, rfl⟩ := scalar returned success
      trivial) (identity_relocates_value logical physical rename layout.runtime left right leftInside rightInside)
  exact raw.protectGenerator stack stackInside

/-- Extract the actual next state and its invariant for a following operation. -/
theorem Preserves.next {logical physical : Mutable.Heap} {rename : Nat → Nat} {anchors : Nat}
    {next : State} {right : Step State Mutable.Completion}
    (preserved : Preserves logical physical rename anchors (.next next) right)
    (globals : Mutable.Globals) (globalsInside : GlobalsWithin logical.length globals) :
    ∃ physicalAfter nextMap,
      (∀ address < logical.length, nextMap address = rename address) ∧
      logical.length ≤ next.heap.length ∧ physical.length ≤ physicalAfter.length ∧
      ExecutionLayout next.heap physicalAfter nextMap ∧ StateWithin next ∧
      GlobalsWithin next.heap.length globals ∧ relocateGlobals nextMap globals = relocateGlobals rename globals ∧
      right = .next (relocateState nextMap physicalAfter next) := by
  obtain ⟨logicalAfter, physicalAfter, nextMap, agree, grows, physicalGrows, layout, heap, inside, paired⟩ := preserved
  change next.heap = logicalAfter at heap
  subst logicalAfter
  exact ⟨physicalAfter, nextMap, agree, grows, physicalGrows, layout, inside,
    globalsInside.mono grows, relocateGlobals_congr nextMap rename logical.length globals agree globalsInside, paired⟩

end FormalSW.PyAst.HeapCalls.Relocation

