import lang.py.FormalSW.Runtime
import lang.py.builtin.type.int

namespace FormalSW.PyAst.Math

/-- Method lookup succeeds for integers and booleans; other scalar types lack it. -/
def bitLengthCall (value : Constant) : Except ExceptionObject Constant :=
  match scalarNumber value with
  | some n => .ok (.int (FormalSW.Py.Builtin.Int.bitLength n))
  | none => .error { typeName := "AttributeError", args := [] }

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

/-- Python's variadic gcd accepts integer indices, including Booleans, and
returns a nonnegative integer. Every argument is checked even after reaching 1. -/
def gcdCall (values : List Constant) : Except ExceptionObject Constant := do
  let integers ← values.mapM fun value =>
    match scalarNumber value with
    | some n => .ok n.natAbs
    | none => .error { typeName := "TypeError", args := [] }
  return .int ((integers.foldl Nat.gcd 0 : Nat) : Int)

theorem gcdCall_pair (a b : Int) :
    gcdCall [.int a, .int b] = .ok (.int (Nat.gcd a.natAbs b.natAbs)) := by
  change Except.ok (Constant.int ((Nat.gcd (Nat.gcd 0 a.natAbs) b.natAbs : Nat) : Int)) = _
  simp

/-- Exact multiplicative recurrence for the coefficient `(offset + k) choose k`.
The recursion follows the number of factors, without an input or fuel cutoff. -/
def combProduct (offset : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => combProduct offset k * (offset + k + 1) / (k + 1)

/-- Symmetry keeps the number of factors small even for large `k` near `n`. -/
def comb (n k : Nat) : Nat :=
  if k > n then 0 else
    let count := min k (n - k)
    combProduct (n - count) count

/-- Both integer-index conversions precede validation of negative arguments. -/
def combCall : List Constant → Except ExceptionObject Constant
  | [n, k] =>
      match scalarNumber n, scalarNumber k with
      | some n, some k =>
          if n < 0 ∨ k < 0 then .error { typeName := "ValueError", args := [] }
          else .ok (.int (comb n.toNat k.toNat))
      | _, _ => .error { typeName := "TypeError", args := [] }
  | _ => .error { typeName := "TypeError", args := [] }

theorem combCall_naturals (n k : Nat) :
    combCall [.int n, .int k] = .ok (.int (comb n k)) := by
  simp [combCall]

end FormalSW.PyAst.Math

namespace FormalSW.PyAst

/-- Module members with executable standard-library models. The bound name
includes the module alias, keeping it distinct from Python function names. -/
def moduleImports (names : List (String × String)) : List ((String × String) × String) :=
  names.flatMap fun (library, alias) =>
    if library = "math" then [((library, "isqrt"), alias ++ ".isqrt"),
      ((library, "gcd"), alias ++ ".gcd"), ((library, "comb"), alias ++ ".comb")]
    else []

/-- Source import bindings are retained in the AST, including aliases. -/
def importedFunction (body : List Stmt) (binding : String) : Option (String × String) :=
  match body with
  | [] => none
  | .importFrom library names :: rest =>
      match names.find? (fun name => name.2 == binding) with
      | some (name, _) => some (library, name)
      | none => importedFunction rest binding
  | .importModules names :: rest =>
      match (moduleImports names).find? (fun name => name.2 == binding) with
      | some (function, _) => some function
      | none => importedFunction rest binding
  | _ :: rest => importedFunction rest binding

def libraryFunction (module : Module) (name : String) :
    Option (List Constant → Except ExceptionObject Constant) :=
  match importedFunction module.body name with
  | some ("math", "isqrt") => some Math.isqrtCall
  | some ("math", "gcd") => some Math.gcdCall
  | some ("math", "comb") => some Math.combCall
  | _ => none

def libraryCall (module : Module) (name : String) (values : List Constant) :
    Option (Except ExceptionObject Constant) :=
  (libraryFunction module name).map (fun function => function values)

end FormalSW.PyAst
