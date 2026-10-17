import FormalSW
open FormalSW.PyAst

private def cell : SharedLocation := .item (.name "data") (.constant (.int 0))
private def increment : List ParallelOp :=
  [.read "n" cell, .write cell (.binOp (.name "n") .add (.constant (.int 1)))]
private def worker (program : List ParallelOp) (lock : Nat := 0) : Option ParallelWorker :=
  some ⟨program, [("data", .ref 0), ("mutex", .lock lock)]⟩
private def initial (n : Int) : SharedState := { objects := [.array [.int n]] }

example : Ensures(Parallel([], initial 7), fun state => state = initial 7) := by native_decide
example : CanReturn(Parallel([worker increment], initial 7), initial 8) := by native_decide
example : CanReturn(Parallel(List.replicate 2 (worker increment), initial 0), initial 1) := by native_decide
example : CanReturn(Parallel(List.replicate 2 (worker increment), initial 0), initial 2) := by native_decide

private def lockedIncrement := [.acquire (.name "mutex")] ++ increment ++ [.release (.name "mutex")]
-- The same mutex excludes the lost update; distinct mutexes do not.
example : Ensures(Parallel(List.replicate 2 (worker lockedIncrement), initial 0),
    fun state => state = initial 2) := by native_decide
example : CanReturn(Parallel([worker lockedIncrement 0, worker lockedIncrement 1], initial 0), initial 1) := by native_decide

-- Locks are non-reentrant. Missing releases and invalid unlocks fail guarantees.
example : ¬ Ensures(Parallel([worker [.acquire (.name "mutex"), .acquire (.name "mutex")]], initial 0), fun _ => True) := by native_decide
example : ¬ Ensures(Parallel(List.replicate 2 (worker [.acquire (.name "mutex")]), initial 0), fun _ => True) := by native_decide
example : ¬ Ensures(Parallel([worker [.release (.name "mutex")]], initial 0), fun _ => True) := by native_decide
example : ¬ Ensures(Parallel([none], initial 0), fun _ => True) := by native_decide
example : parallelExplore 0 ⟨initial 0, [⟨increment, [("data", .ref 0)]⟩]⟩ = [.error .incomplete] := rfl
example : ¬ Ensures(Parallel([worker [.write cell (.binOp (.constant (.int 1)) .floorDiv
    (.constant (.int 0)))]], initial 0), fun _ => True) := by native_decide

-- Negative and nonzero indices use ordinary Python list indexing.
example : CanReturn(Parallel([some ⟨[.write (.item (.name "a") (.constant (.int (-1))))
    (.constant (.int 9))], [("a", .ref 0)]⟩], { objects := [.array [.int 3, .int 4]] }),
    { objects := [.array [.int 3, .int 9]] }) := by native_decide
-- Out-of-bounds indexing is an exception, not a silently ignored operation.
example : ¬ Ensures(Parallel([some ⟨[.read "n" (.item (.name "a") (.constant (.int 4)))],
    [("a", .ref 0)]⟩], initial 0), fun _ => True) := by native_decide

-- An alias loaded from a field must refer to the same mutable object.
example : CanReturn(Parallel([some ⟨[
    .read "alias" (.field (.name "root") "next"),
    .write (.field (.name "alias") "value") (.constant (.int 7))], [("root", .ref 0)]⟩],
    { objects := [.object [("next", .ref 1)], .object [("value", .int 0)]] }),
    { objects := [.object [("next", .ref 1)], .object [("value", .int 7)]] }) := by native_decide
-- Plain field errors and missing heap identities cannot satisfy a guarantee.
example : ¬ Ensures(Parallel([some ⟨[.read "x" (.field (.name "p") "absent")],
    [("p", .ref 0)]⟩], { objects := [.object []] }), fun _ => True) := by native_decide
example : ¬ Ensures(Parallel([worker increment], {}), fun _ => True) := by native_decide

-- A missing path cannot masquerade as an unequal reference in Sometimes.
example : SharedState.readPath { objects := [.object [("next", .none)]] }
    (.ref 0) ["next", "prev"] = none := rfl

-- Trial assertions reuse the interpreter's integer-list indexing semantics.
example : PyTrial.readIntItem { objects := [.array [.int 7, .int 9]] } 0 (-1) = some 9 := by decide
example : PyTrial.readIntItem { objects := [.array [.int 7, .int 9]] } 0 (-3) = none := by decide
example : PyTrial.readIntItem { objects := [.array [.int 7, .int 9]] } 0 2 = none := by decide
example : PyTrial.readIntItem { objects := [.array [.bool true]] } 0 0 = none := by decide
