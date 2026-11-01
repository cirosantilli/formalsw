import lang.py.FormalSW.Model

/-! Nested name targets unpack one sequence level at a time. Private names retain
the outer fields while inner targets bind their names from left to right. -/
namespace FormalSW.PyAst.UnpackingTargets

def temporary (stem : String) (position : Nat) : String :=
  stem ++ "." ++ toString position

def names (stem : String) (count : Nat) : List Expr :=
  (List.range count).map fun position => .name (temporary stem position)

mutual
  def lower (target source : Expr) (stem : String) : List Stmt :=
    match target with
    | .name name => [.assign [.name name] source]
    | .tuple targets | .list targets =>
        .assign [.tuple (names stem targets.length)] source :: children targets stem 0
    | _ => [.unsupported "unsupported unpacking target"]
  termination_by sizeOf target

  def children (targets : List Expr) (stem : String) (position : Nat) : List Stmt :=
    match targets with
    | [] => []
    | target :: rest =>
        lower target (.name (temporary stem position)) (temporary stem position) ++
          children rest stem (position + 1)
  termination_by sizeOf targets
end

def assignment (targets : List Expr) (source : Expr) : List Stmt :=
  lower (.tuple targets) source "$formalsw.target"

mutual
  theorem lower_forall (predicate : Stmt → Prop)
      (assign : ∀ targets value, predicate (.assign targets value))
      (unsupported : ∀ reason, predicate (.unsupported reason))
      (target source : Expr) (stem : String) :
      ∀ statement ∈ lower target source stem, predicate statement := by
    cases target with
    | name name => simpa only [lower, List.mem_singleton, forall_eq] using assign [.name name] source
    | tuple targets | list targets =>
        intro statement member
        simp only [lower, List.mem_cons] at member
        rcases member with rfl | member
        · exact assign _ _
        · exact children_forall predicate assign unsupported targets stem 0 statement member
    | _ => simpa only [lower, List.mem_singleton, forall_eq] using unsupported "unsupported unpacking target"
  termination_by sizeOf target

  theorem children_forall (predicate : Stmt → Prop)
      (assign : ∀ targets value, predicate (.assign targets value))
      (unsupported : ∀ reason, predicate (.unsupported reason))
      (targets : List Expr) (stem : String) (position : Nat) :
      ∀ statement ∈ children targets stem position, predicate statement := by
    cases targets with
    | nil => simp [children]
    | cons target rest =>
        intro statement member
        simp only [children, List.mem_append] at member
        rcases member with member | member
        · exact lower_forall predicate assign unsupported target _ _ statement member
        · exact children_forall predicate assign unsupported rest stem (position + 1) statement member
  termination_by sizeOf targets
end

end FormalSW.PyAst.UnpackingTargets
