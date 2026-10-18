import lang.py.FormalSW.Runtime

namespace FormalSW.PyAst.Math

/-- Binary search for the integer square root. The interval, rather than a
fixed machine word or evaluation budget, bounds the recursion. -/
def sqrtSearch (n lo hi : Nat) : Nat :=
  if gap : lo + 1 < hi then
    let mid := (lo + hi) / 2
    if mid * mid ≤ n then sqrtSearch n mid hi
    else sqrtSearch n lo mid
  else lo
termination_by hi - lo
decreasing_by all_goals omega

theorem sqrtSearch_spec (n lo hi : Nat) (ordered : lo < hi)
    (lower : lo * lo ≤ n) (upper : n < hi * hi) :
    sqrtSearch n lo hi * sqrtSearch n lo hi ≤ n ∧
      n < (sqrtSearch n lo hi + 1) * (sqrtSearch n lo hi + 1) := by
  induction measure : hi - lo using Nat.strongRecOn generalizing lo hi with
  | ind size ih =>
      rw [sqrtSearch.eq_1]
      by_cases gap : lo + 1 < hi
      · simp only [gap, ↓reduceDIte]
        by_cases middle : ((lo + hi) / 2) * ((lo + hi) / 2) ≤ n
        · simp only [middle, ↓reduceIte]
          exact ih (hi - (lo + hi) / 2) (by omega) ((lo + hi) / 2) hi
            (by omega) middle upper rfl
        · simp only [middle, ↓reduceIte]
          exact ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2)
            (by omega) lower (by omega) rfl
      · simp only [gap, ↓reduceDIte]
        have : hi = lo + 1 := by omega
        exact ⟨lower, by simpa [this] using upper⟩

def isqrt (n : Nat) : Nat := sqrtSearch n 0 (n + 1)

/-- The characterization used to connect this model to existing mathematical
square-root libraries, without requiring those libraries as dependencies. -/
theorem isqrt_spec (n : Nat) :
    isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1) :=
  sqrtSearch_spec n 0 (n + 1) (by omega) (by simp)
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_mul_self (n + 1)))

def isqrtCall : List Constant → Except ExceptionObject Constant
  | [.int n] =>
      if n < 0 then .error { typeName := "ValueError", args := [] }
      else .ok (.int (isqrt n.toNat))
  | [.bool value] => .ok (.int (if value then 1 else 0))
  | _ => .error { typeName := "TypeError", args := [] }

end FormalSW.PyAst.Math

namespace FormalSW.PyAst

/-- Source import bindings are retained in the AST, including aliases. -/
def importedFunction (body : List Stmt) (binding : String) : Option (String × String) :=
  match body with
  | [] => none
  | .importFrom library names :: rest =>
      match names.find? (fun name => name.2 == binding) with
      | some (name, _) => some (library, name)
      | none => importedFunction rest binding
  | _ :: rest => importedFunction rest binding

def libraryCall (module : Module) (name : String) (values : List Constant) :
    Option (Except ExceptionObject Constant) :=
  match importedFunction module.body name with
  | some ("math", "isqrt") => some (Math.isqrtCall values)
  | _ => none

end FormalSW.PyAst
