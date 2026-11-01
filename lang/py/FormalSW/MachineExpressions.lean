import lang.py.FormalSW.ArithmeticRelocation
import lang.py.FormalSW.ClassCalls

/-! Expression steps preserve shared references and the order of operand effects. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_scalar_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (outcome : Option (Except ExceptionObject Constant))
    (stack : List Frame) (globals : Mutable.Globals) :
    result (globals := relocateGlobals rename globals) physicalAnchors physical (scalarResult outcome)
        (stack.map (relocateFrame rename)) =
      relocateStep rename physical physicalAnchors
        (result (globals := globals) logicalAnchors logical (scalarResult outcome) stack) := by
  cases outcome with
  | none => rfl
  | some outcome =>
    cases outcome <;>
      simp [result, run, scalarResult, done, relocateStep, relocateState, relocateWork, relocateCompletion, Except.map, relocateValue]

theorem result_scalar_within (heap : Mutable.Heap) (anchors : Nat)
    (outcome : Option (Except ExceptionObject Constant)) (stack : List Frame) (globals : Mutable.Globals)
    (stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame)
    (globalsInside : GlobalsWithin heap.length globals) :
    StepWithin (result (globals := globals) anchors heap (scalarResult outcome) stack) := by
  cases outcome with
  | none => trivial
  | some outcome =>
    cases outcome with
    | error exception =>
      exact ⟨globalsInside, by intro value impossible; cases impossible⟩
    | ok scalar => exact ⟨by trivial, stackInside⟩

theorem step_binary_scalars_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (op : BinOp) (left right : Constant) (inPlace : Bool)
    (stack : List Frame) (globals : Mutable.Globals)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value (.scalar right), .binaryRight op (.scalar left) inPlace :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value (.scalar right), .binaryRight op (.scalar left) inPlace :: stack, logical⟩ globals) ∧
      StepWithin (step module logicalAnchors
        ⟨.value (.scalar right), .binaryRight op (.scalar left) inPlace :: stack, logical⟩ globals) := by
  have transported := result_scalar_relocates logical physical rename logicalAnchors physicalAnchors
    (scalarBinary op left right) stack globals
  constructor
  · cases inPlace <;>
      simp only [relocateState, relocateWork, List.map_cons, relocateFrame, relocateValue, step, inplace,
        binary_scalars, Bool.false_eq_true, if_false, if_true] <;>
      rw [transported] <;>
      exact protectGenerator_relocates rename physical physicalAnchors _ _
  · cases inPlace <;> apply protectGenerator_within <;>
      simpa only [inplace, binary_scalars] using
        result_scalar_within logical logicalAnchors (scalarBinary op left right) stack globals stackInside globalsInside

theorem step_unary_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (op : UnaryOp) (value : Value) (stack : List Frame) (globals : Mutable.Globals)
    (inside : value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals)
    (outcome : Except ExceptionObject Value) (after : Mutable.Heap)
    (executed : unary op value logical = some (outcome, after)) :
    after = logical ∧
      step module physicalAnchors (relocateState rename physical ⟨.value value, .unary op :: stack, logical⟩)
          (relocateGlobals rename globals) =
        relocateStep rename physical physicalAnchors
          (step module logicalAnchors ⟨.value value, .unary op :: stack, logical⟩ globals) ∧
      StepWithin (step module logicalAnchors ⟨.value value, .unary op :: stack, logical⟩ globals) := by
  obtain ⟨same, scalar⟩ := unary_effect logical after op value inside outcome executed
  subst after
  have paired := unary_relocates logical physical rename layout op value inside
  rw [executed] at paired
  refine ⟨rfl, ?_, ?_⟩
  · have transported := result_relocates rename logical physical logical physical logicalAnchors physicalAnchors
      (unary op value) (unary op (relocateValue rename value)) stack globals outcome executed paired
    simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step]
    rw [transported]
    simpa only [List.map_cons, relocateFrame] using
      protectGenerator_relocates rename physical physicalAnchors (.unary op :: stack) _
  · apply protectGenerator_within
    apply result_within logicalAnchors logical logical _ stack globals outcome executed (Nat.le_refl _) _ stackInside globalsInside
    intro returned success
    obtain ⟨constant, rfl⟩ := scalar returned success
    trivial

theorem step_binaryLeft_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (op : BinOp) (right : Expr) (env : Env)
    (inPlace : Bool) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value value, .binaryLeft op right env inPlace :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .binaryLeft op right env inPlace :: stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step, protectGenerator_next, relocateStep]

theorem StateWithin.binaryLeft (heap : Mutable.Heap) (value : Value) (op : BinOp) (right : Expr) (env : Env)
    (inPlace : Bool) (stack : List Frame)
    (inside : StateWithin ⟨.value value, .binaryLeft op right env inPlace :: stack, heap⟩) :
    StateWithin ⟨.expr right env, .binaryRight op value inPlace :: stack, heap⟩ := by
  have saved := inside.2 (.binaryLeft op right env inPlace) (by simp)
  simp only [FrameWithin] at saved
  refine ⟨saved, ?_⟩
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · simpa only [FrameWithin] using inside.1
  · exact inside.2 frame (by simp [member])

theorem step_binary_expression_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (left right : Expr) (op : BinOp) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors (relocateState rename physical ⟨.expr (.binOp left op right) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.expr (.binOp left op right) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, step, protectGenerator_next, relocateStep, List.map_cons, relocateFrame]

theorem StateWithin.binary_expression (heap : Mutable.Heap) (left right : Expr) (op : BinOp) (env : Env)
    (stack : List Frame) (inside : StateWithin ⟨.expr (.binOp left op right) env, stack, heap⟩) :
    StateWithin ⟨.expr left env, .binaryLeft op right env false :: stack, heap⟩ := by
  refine ⟨inside.1, ?_⟩
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · simpa only [FrameWithin] using inside.1
  · exact inside.2 frame member

theorem step_unary_expression_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (op : UnaryOp) (operand : Expr) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors (relocateState rename physical ⟨.expr (.unaryOp op operand) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.expr (.unaryOp op operand) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, step, protectGenerator_next, relocateStep, List.map_cons, relocateFrame]

theorem StateWithin.unary_expression (heap : Mutable.Heap) (op : UnaryOp) (operand : Expr) (env : Env)
    (stack : List Frame) (inside : StateWithin ⟨.expr (.unaryOp op operand) env, stack, heap⟩) :
    StateWithin ⟨.expr operand env, .unary op :: stack, heap⟩ := by
  refine ⟨inside.1, ?_⟩
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · simp only [FrameWithin]
  · exact inside.2 frame member

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.HeapCalls

/-- Augmented field assignment reads the old value before evaluating its right operand. -/
theorem BlockContinues.augAttribute {globals : Mutable.Globals} {module : Module} {env : Env}
    {base expression : Expr} {name : String} {op : BinOp} {heap afterBase afterRead afterRhs afterOp finalHeap : Heap}
    {receiver previous rhs updated : Value}
    (target : Evaluates (globals := globals) module env base heap receiver afterBase)
    (read : getAttribute module receiver name afterBase = some (.ok previous, afterRead))
    (right : Evaluates (globals := globals) module env expression afterRead rhs afterRhs)
    (operation : inplace op previous rhs afterRhs = some (.ok updated, afterOp))
    (write : Mutable.writeField receiver name updated afterOp = some (.ok (.scalar .none), finalHeap)) :
    BlockContinues (globals := globals) module env [.augAssign (.attribute base name) op expression] heap env finalHeap := by
  intro following anchors stack
  apply Reaches.next rfl
  apply (target anchors _).trans
  apply Reaches.next (following := ⟨.expr expression env,
    .binaryRight op previous true :: .writeAttribute receiver name following env :: stack, afterRead⟩)
    (by simp [step, run, read])
  apply (right anchors _).trans
  apply Reaches.next (following := ⟨.value updated, .writeAttribute receiver name following env :: stack, afterOp⟩)
    (by simp [step, result, run, operation])
  exact .next (following := ⟨.value (.scalar .none), .discard following env :: stack, finalHeap⟩)
    (by simp [step, result, run, write]) (.next rfl .refl)

end FormalSW.PyAst.HeapCalls
