import «.cleanxy».tests.py.«parallel_trial.py.ast»
import CleanXY

open CleanXY.PyAst

namespace tests.py.parallel_trial

open Concurrent

private def program (item : Nat) : List Op × Concurrent.Env :=
  ([.write "item" "value" "item"], [("item", some item)])

private theorem assertions (heap : Heap) (items : List Nat)
    (marked : ∀ item ∈ items, heap item "value" = some item) :
    items.foldlM (fun (_ : Unit) item => do
      check ((← read heap (some item) "value") == some item)
      pure ()) () = some () := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      have head := marked item (by simp)
      have tail := ih (by intro node member; exact marked node (by simp [member]))
      simpa [List.foldlM_cons, Concurrent.read, check, head] using tail

private theorem all_marked (items : List Nat) (heap : Heap) :
    LockedEnsures program (fun final => ∀ item ∈ items, final item "value" = some item)
      items none heap := by
  let I := fun (pending : List Nat) (heap : Heap) => ∀ item ∈ items, item ∉ pending → heap item "value" = some item
  apply invariant program I
  · intro final done item member
    exact done item member (by simp)
  · intro before job after state previous
    refine ⟨put state job "value" (some job), ?_, ?_⟩
    · simp [program, execute, step]
    · intro item member absent
      by_cases same : item = job
      · subst item; simp [put]
      · have already : item ∉ before ++ job :: after := by simpa [same] using absent
        simpa [put, same] using previous item member already
  · intro item member absent
    exact False.elim (absent member)

theorem mark.«Concurrent(check_marks)» :
    ∀ (count : Int) (items : List Nat),
    ([] ++ items).Nodup →
    items.length = count.toNat →
    Concurrent.Ensures ParallelTrialAst.module "mark"
    ["item"] "mutex" (fun _job => [some (_job)])
    (items) ((fun (_ : Nat) (_ : String) => (none : Option Nat))) (fun _final => ((do let _result3 ← (items).foldlM (fun _state1 (_item2 : Nat) => do Concurrent.check (((← Concurrent.read _final (some (_item2)) "value")) == (some (_item2))); pure ()) (()); pure ()) : Option Unit) = some ())
  := by
  intro count items _fresh _length
  refine ⟨[.write "item" "value" "item"], by decide, ?_⟩
  apply LockedEnsures.mono (proof := all_marked items (fun _ _ => none))
  intro final marked
  have passed := assertions final items marked
  change ((do let _ ← items.foldlM (fun (_ : Unit) item => do check ((← Concurrent.read final (some item) "value") == some item); pure ()) (); pure ()) : Option Unit) = some ()
  rw [passed]
  rfl

end tests.py.parallel_trial
