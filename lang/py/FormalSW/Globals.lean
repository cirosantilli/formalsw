import lang.py.FormalSW.Runtime

namespace FormalSW.PyAst

abbrev ScalarGlobals := List (String × Constant)

/-- Both normal and exceptional completion retain the observable module state. -/
structure ScalarCompletion where
  outcome : Except ExceptionObject Constant
  globals : ScalarGlobals
deriving Repr, DecidableEq

/-- A stateful call uses an internal execution whose returned value records the
Python outcome and final state. User-facing predicates inspect that outcome. -/
structure ScalarCall where
  execution : Execution ScalarCompletion

namespace ScalarCall

def Finishes (call : ScalarCall) (outcome : Except ExceptionObject Constant)
    (globals : ScalarGlobals) : Prop :=
  PyAst.Finishes call.execution.step call.execution.initial (.ok ⟨outcome, globals⟩)

def Returns (call : ScalarCall) : Prop := ∃ value globals, call.Finishes (.ok value) globals
def Throws (call : ScalarCall) : Prop := ∃ exception globals, call.Finishes (.error exception) globals
def Halts (call : ScalarCall) : Prop := ∃ outcome globals, call.Finishes outcome globals
def Diverges (call : ScalarCall) : Prop := call.execution.Diverges

def Equiv (left right : ScalarCall) : Prop :=
  ∀ outcome globals, left.Finishes outcome globals ↔ right.Finishes outcome globals

def EquivReturn (left right : ScalarCall) : Prop :=
  ∀ a ga b gb, left.Finishes (.ok a) ga → right.Finishes (.ok b) gb → a = b ∧ ga = gb

def ReturnType (call : ScalarCall) (kind : String) : Prop :=
  call.Throws ∨ ∃ value globals, call.Finishes (.ok value) globals ∧
    (match value with
      | .int _ => kind = "int"
      | .string _ => kind = "str"
      | .bool _ => kind = "bool"
      | .none => kind = "None")

theorem throws_halts {call : ScalarCall} (h : call.Throws) : call.Halts := by
  obtain ⟨exception, globals, finished⟩ := h
  exact ⟨.error exception, globals, finished⟩

theorem diverges_not_halts {call : ScalarCall} (h : call.Diverges) : ¬ call.Halts := by
  rintro ⟨outcome, globals, finished⟩
  exact Execution.diverges_not_halts h ⟨.ok ⟨outcome, globals⟩, finished⟩

theorem returns_iff_halts_not_throws (call : ScalarCall) :
    call.Returns ↔ call.Halts ∧ ¬ call.Throws := by
  constructor
  · rintro ⟨value, globals, returned⟩
    refine ⟨⟨.ok value, globals, returned⟩, ?_⟩
    rintro ⟨exception, other, thrown⟩
    have impossible := returned.unique thrown
    cases impossible
  · rintro ⟨⟨outcome, globals, done⟩, noThrow⟩
    cases outcome with
    | ok value => exact ⟨value, globals, done⟩
    | error exception => exact False.elim (noThrow ⟨exception, globals, done⟩)

theorem Equiv.returns_iff {left right : ScalarCall} (h : left.Equiv right) : left.Returns ↔ right.Returns := by
  constructor <;> rintro ⟨value, globals, done⟩
  · exact ⟨value, globals, (h _ _).mp done⟩
  · exact ⟨value, globals, (h _ _).mpr done⟩

theorem Equiv.halts_iff {left right : ScalarCall} (h : left.Equiv right) : left.Halts ↔ right.Halts := by
  constructor <;> rintro ⟨outcome, globals, done⟩
  · exact ⟨outcome, globals, (h _ _).mp done⟩
  · exact ⟨outcome, globals, (h _ _).mpr done⟩

theorem finishes_of_observe {call : ScalarCall} (h : call.execution.observe fuel = .done (.ok ⟨outcome, globals⟩)) :
    call.Finishes outcome globals := Execution.finishes_of_observe h

theorem equiv_of_finishes {left right : ScalarCall}
    (hl : left.Finishes outcome globals) (hr : right.Finishes outcome globals) : left.Equiv right := by
  intro actual state
  constructor
  · intro h
    have eq := Except.ok.inj (h.unique hl)
    have outcomeEq := congrArg ScalarCompletion.outcome eq
    have stateEq := congrArg ScalarCompletion.globals eq
    cases outcomeEq
    cases stateEq
    exact hr
  · intro h
    have eq := Except.ok.inj (h.unique hr)
    have outcomeEq := congrArg ScalarCompletion.outcome eq
    have stateEq := congrArg ScalarCompletion.globals eq
    cases outcomeEq
    cases stateEq
    exact hl

theorem Equiv.equivReturn {left right : ScalarCall} (h : left.Equiv right) : left.EquivReturn right := by
  intro a ga b gb ha hb
  have eq := Except.ok.inj (((h _ _).mp ha).unique hb)
  exact ⟨Except.ok.inj (congrArg ScalarCompletion.outcome eq), congrArg ScalarCompletion.globals eq⟩

end ScalarCall

mutual
  /-- Scope declarations apply to the whole function, including dead branches. -/
  def declaredGlobals : Stmt → List String
    | .globalDecl names => names
    | .ifThen _ yes no | .whileDo _ yes no | .forIn _ _ yes no =>
        blockGlobals yes ++ blockGlobals no
    | _ => []
  def blockGlobals : List Stmt → List String
    | [] => []
    | first :: rest => declaredGlobals first ++ blockGlobals rest
end

mutual
  def assignedLocals : Stmt → List String
    | .assign [.name name] _ | .annAssign (.name name) _ _ | .augAssign (.name name) _ _ => [name]
    | .forIn (.name name) _ body otherwise => name :: (blockLocals body ++ blockLocals otherwise)
    | .ifThen _ yes no | .whileDo _ yes no => blockLocals yes ++ blockLocals no
    | _ => []
  def blockLocals : List Stmt → List String
    | [] => []
    | first :: rest => assignedLocals first ++ blockLocals rest
end

def globalsStep (initial : ScalarGlobals) (declared : List String)
    (state : ScalarState) : Step ScalarState ScalarCompletion :=
  match state.todo with
  | .globalDecl _ :: rest => .next ⟨rest, state.env⟩
  | _ => match scalarStep state with
      | .next following => .next following
      | .unsupported => .unsupported
      | .done outcome => .done (.ok ⟨outcome, initial.map fun (name, old) =>
          (name, if name ∈ declared then (state.env name).getD old else old)⟩)

/-- Globals are explicit call-entry inputs. Locals shadow them according to
Python's whole-function scope, and only declared global assignments change the
reported state. Extra supplied globals are preserved, allowing two functions
with different footprints to be compared in the same initial world. -/
def scalarFunctionWithGlobals (module : Module) (name : String) (values : List Constant)
    (globals : ScalarGlobals) : ScalarCall :=
  ⟨match findFunctionIn module.body name with
  | none => Execution.unsupported
  | some (args, body) =>
      let declared := blockGlobals body
      let locals := blockLocals body |>.filter (fun name => name ∉ declared)
      if args.length = values.length ∧ (globals.map Prod.fst).Nodup ∧
          declared.all (fun name => (globals.lookup name).isSome) then
        let env : ScalarEnv := fun name =>
          if name ∈ args.map Arg.name then argumentEnv args values name
          else if name ∈ locals then none else globals.lookup name
        ⟨ScalarState, ⟨executableBody body, env⟩, globalsStep globals declared⟩
      else Execution.unsupported⟩

end FormalSW.PyAst
