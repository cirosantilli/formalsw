import «.formalsw».tests.py.«parallel_doubly_linked_list.py.ast»
import FormalSW

open FormalSW.PyAst

open Concurrent

namespace LinkedInsertion

-- Private mathematical lemmas for this example, not specification primitives.
def Chain (next prev : String) (heap : Heap) (left : Option Nat) : List Nat → Option Nat → Prop
  | [], _ => True
  | node :: rest, right =>
      heap node prev = left ∧ heap node next = rest.head?.or right ∧
      Chain next prev heap (some node) rest right

theorem Chain.congr {next prev : String} {heap other : Heap} {nodes : List Nat}
    (same : ∀ node ∈ nodes, ∀ field, other node field = heap node field)
    {left right : Option Nat} (chain : Chain next prev heap left nodes right) :
    Chain next prev other left nodes right := by
  induction nodes generalizing left with
  | nil => trivial
  | cons node rest ih =>
      rcases chain with ⟨backward, forward, tail⟩
      exact ⟨(same node (by simp) prev).trans backward,
        (same node (by simp) next).trans forward,
        ih (fun n hn => same n (by simp [hn])) tail⟩

def insert (next prev : String) (heap : Heap) (head node following : Nat) : Heap :=
  put (put (put (put heap node prev (some head)) node next (some following))
    head next (some node)) following prev (some node)

theorem Chain.insert_preserves {next prev : String} (fields : next ≠ prev)
    {heap : Heap} {head node following : Nat} {rest : List Nat}
    (distinct : (head :: following :: rest).Nodup)
    (fresh : node ∉ head :: following :: rest)
    (chain : Chain next prev heap none (head :: following :: rest) none) :
    Chain next prev (insert next prev heap head node following) none
      (head :: node :: following :: rest) none := by
  simp only [List.nodup_cons, List.mem_cons, not_or] at distinct fresh
  rcases distinct with ⟨⟨headFollowing, headRest⟩, followingRest, restDistinct⟩
  rcases fresh with ⟨nodeHead, nodeFollowing, nodeRest⟩
  rcases chain with ⟨headPrev, headNext, followingPrev, followingNext, tail⟩
  have tail' : Chain next prev (insert next prev heap head node following)
      (some following) rest none := tail.congr (by
    intro address member field
    have hn : address ≠ node := by intro e; subst address; exact nodeRest member
    have hh : address ≠ head := by intro e; subst address; exact headRest member
    have hf : address ≠ following := by intro e; subst address; exact followingRest member
    simp [insert, put, hn, hh, hf])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, tail'⟩ <;>
    simp_all [insert, put, Ne.symm]


def ops : List Op :=
  [.read "following" "head" "next", .write "node" "prev" "head",
   .write "node" "next" "following", .yield, .write "head" "next" "node",
   .write "following" "prev" "node"]

def program (head node : Nat) : List Op × Concurrent.Env :=
  (ops, [("head", some head), ("node", some node)])

theorem execution (heap : Heap) (head node following : Nat)
    (link : heap head "next" = some following) :
    execute ops heap (program head node).2 =
      some (insert "next" "prev" heap head node following) := by
  simp [ops, program, execute, step, List.lookup, link, LinkedInsertion.insert]

def Inv (head tail : Nat) (existing inserted pending : List Nat) (heap : Heap) : Prop :=
  ∃ order, (order ++ pending).Perm inserted ∧
    Chain "next" "prev" heap none (head :: (order ++ existing ++ [tail])) none

theorem resources {head tail node : Nat} {before after order existing inserted : List Nat}
    (distinct : (head :: (inserted ++ existing ++ [tail])).Nodup)
    (perm : (order ++ (before ++ node :: after)).Perm inserted) :
    (head :: (order ++ existing ++ [tail])).Nodup ∧
    node ∉ head :: (order ++ existing ++ [tail]) := by
  have allDistinct := ((perm.append_right (existing ++ [tail])).cons head).nodup_iff.mpr (by simpa [List.append_assoc] using distinct)
  simp only [List.nodup_cons, List.nodup_append, List.mem_append, List.mem_cons,
    not_or, List.append_assoc] at allDistinct ⊢
  grind

theorem preserved (head tail : Nat) (existing inserted : List Nat)
    (distinct : (head :: (inserted ++ existing ++ [tail])).Nodup)
    (before : List Nat) (node : Nat) (after : List Nat) (heap : Heap)
    (initial : Inv head tail existing inserted (before ++ node :: after) heap) :
    ∃ final, execute (program head node).1 heap (program head node).2 = some final ∧
      Inv head tail existing inserted (before ++ after) final := by
  obtain ⟨order, perm, chain⟩ := initial
  obtain ⟨currentDistinct, fresh⟩ := resources distinct perm
  have moved : ((node :: order) ++ (before ++ after)).Perm inserted := by
    apply List.Perm.trans _ perm
    simpa [List.append_assoc] using
      (List.perm_middle (l₁ := order ++ before) (l₂ := after) (a := node)).symm
  cases members : order ++ existing ++ [tail] with
  | nil => simp at members
  | cons following rest =>
      rw [members] at chain currentDistinct fresh
      have link : heap head "next" = some following := chain.2.1
      refine ⟨insert "next" "prev" heap head node following, execution heap head node following link, ?_⟩
      refine ⟨node :: order, moved, ?_⟩
      simpa only [List.cons_append, members] using
        Chain.insert_preserves (by decide : "next" ≠ "prev") currentDistinct fresh chain

theorem all_insertions (head tail : Nat) (existing inserted : List Nat) (heap : Heap)
    (distinct : (head :: (inserted ++ existing ++ [tail])).Nodup)
    (chain : Chain "next" "prev" heap none (head :: (existing ++ [tail])) none) :
    LockedEnsures (program head)
      (fun final => ∃ order, order.Perm inserted ∧
        (head :: (order ++ existing ++ [tail])).Nodup ∧ Chain "next" "prev" final none (head :: (order ++ existing ++ [tail])) none)
      inserted none heap := by
  apply invariant (program head) (Inv head tail existing inserted)
  · intro final h
    obtain ⟨order, perm, chain⟩ := h
    simp only [List.append_nil] at perm
    refine ⟨order, perm, ?_, chain⟩
    simpa [List.append_assoc] using
      ((perm.append_right (existing ++ [tail])).cons head).nodup_iff.mpr
        (by simpa [List.append_assoc] using distinct)
  · exact preserved head tail existing inserted distinct
  · exact ⟨[], by simp, chain⟩

-- The setup is the ordinary pairwise-assignment loop from run_trial.
def wire (heap : Heap) (nodes : List Nat) : Heap :=
  (nodes.zip (nodes.drop 1)).foldl (fun heap pair =>
    put (put heap pair.1 "next" (some pair.2)) pair.2 "prev" (some pair.1)) heap

@[simp] theorem wire_nil (heap : Heap) : wire heap [] = heap := rfl
@[simp] theorem wire_singleton (heap : Heap) (node : Nat) : wire heap [node] = heap := rfl
@[simp] theorem wire_cons (heap : Heap) (a b : Nat) (rest : List Nat) :
    wire heap (a :: b :: rest) =
      wire (put (put heap a "next" (some b)) b "prev" (some a)) (b :: rest) := rfl

theorem wire_frame (nodes : List Nat) (heap : Heap) (address : Nat) (field : String)
    (outside : address ∉ nodes) : wire heap nodes address field = heap address field := by
  induction nodes generalizing heap with
  | nil => rfl
  | cons a rest ih =>
      cases rest with
      | nil => rfl
      | cons b rest =>
          rw [wire_cons, ih _ (by simp_all)]
          simp only [List.mem_cons, not_or] at outside
          simp [put, outside.1, outside.2.1]

theorem wire_chain (nodes : List Nat) (heap : Heap) (left : Option Nat)
    (distinct : nodes.Nodup)
    (first : ∀ node, nodes.head? = some node → heap node "prev" = left)
    (forward : ∀ node ∈ nodes, heap node "next" = none)
    (backward : ∀ node ∈ nodes.tail, heap node "prev" = none) :
    Chain "next" "prev" (wire heap nodes) left nodes none := by
  induction nodes generalizing heap left with
  | nil => trivial
  | cons a rest ih =>
      cases rest with
      | nil => exact ⟨first a rfl, forward a (by simp), trivial⟩
      | cons b rest =>
          have ha : a ∉ b :: rest := (List.nodup_cons.mp distinct).1
          have hb : b ∉ rest := (List.nodup_cons.mp (List.nodup_cons.mp distinct).2).1
          let updated := put (put heap a "next" (some b)) b "prev" (some a)
          have remaining := ih updated (some a) (List.nodup_cons.mp distinct).2
            (by intro node h; simp only [List.head?_cons, Option.some.injEq] at h; subst node; simp [updated, put])
            (by
              intro node member
              have hna : node ≠ a := by intro h; subst node; exact ha member
              simp [updated, put, hna, forward node (by simp [member])])
            (by
              intro node member
              have hna : node ≠ a := by intro h; subst node; exact ha (by simp_all)
              have hnb : node ≠ b := by intro h; subst node; exact hb member
              simp [updated, put, hna, hnb, backward node (by simp_all)])
          rw [wire_cons]
          refine ⟨?_, ?_, remaining⟩
          · rw [wire_frame _ _ a "prev" ha]
            have hab : a ≠ b := by intro h; subst a; exact ha (by simp)
            simpa [put, hab] using first a rfl
          · rw [wire_frame _ _ a "next" ha]
            have hab : a ≠ b := by intro h; subst a; exact ha (by simp)
            simp [put, hab]

-- Only adjacent-edge facts are needed to verify the actual Python assertions.
def Path (heap : Heap) (current : Nat) : List Nat → Prop
  | [] => True
  | node :: rest => heap current "next" = some node ∧ heap node "prev" = some current ∧ Path heap node rest

theorem Chain.path {heap : Heap} {left right : Option Nat} {head : Nat} {rest : List Nat}
    (chain : Chain "next" "prev" heap left (head :: rest) right) : Path heap head rest := by
  induction rest generalizing head left with
  | nil => trivial
  | cons node rest ih => exact ⟨chain.2.1, chain.2.2.1, ih chain.2.2⟩

theorem Chain.tail_next {heap : Heap} {left : Option Nat} {segment : List Nat} {tail : Nat}
    (chain : Chain "next" "prev" heap left (segment ++ [tail]) none) : heap tail "next" = none := by
  induction segment generalizing left with
  | nil => exact chain.2.1
  | cons _ _ ih => exact ih chain.2.2

def newStep (heap : Heap) (inserted : List Nat) (current : Option Nat) : Option (Option Nat) := do
  let following ← Concurrent.read heap current "next"
  check ((inserted.map some).contains following)
  check ((← Concurrent.read heap following "prev") == current)
  pure following

def oldStep (heap : Heap) (current : Option Nat) (node : Nat) : Option (Option Nat) := do
  check ((← Concurrent.read heap current "next") == some node)
  check ((← Concurrent.read heap (some node) "prev") == current)
  pure (some node)

def assertions (heap : Heap) (head tail : Nat) (existing inserted : List Nat) : Option Unit := do
  let current ← inserted.foldlM (fun current _ => newStep heap inserted current) (some head)
  let _ ← (existing ++ [tail]).foldlM (oldStep heap) current
  check ((← Concurrent.read heap (some head) "prev") == none)
  check ((← Concurrent.read heap (some tail) "next") == none)
  pure ()

theorem fold_ignore_perm {α σ : Type} (step : σ → Option σ) {xs ys : List α}
    (perm : xs.Perm ys) (initial : σ) :
    xs.foldlM (fun state _ => step state) initial = ys.foldlM (fun state _ => step state) initial := by
  induction perm generalizing initial with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldlM_cons]; congr 1; funext state; exact ih state
  | swap => rfl
  | trans _ _ ih₁ ih₂ => exact (ih₁ initial).trans (ih₂ initial)

theorem walk_new (heap : Heap) (allowed segment suffix : List Nat) (start : Nat)
    (path : Path heap start (segment ++ suffix)) (members : ∀ node ∈ segment, node ∈ allowed) :
    ∃ finish, segment.foldlM (fun current _ => newStep heap allowed current) (some start) = some (some finish) ∧
      Path heap finish suffix := by
  induction segment generalizing start with
  | nil => exact ⟨start, rfl, path⟩
  | cons node rest ih =>
      have step : newStep heap allowed (some start) = some (some node) := by
        simp [newStep, Concurrent.read, path.1, path.2.1, check, members node (by simp)]
      obtain ⟨finish, execution, tail⟩ := ih node path.2.2 (fun n hn => members n (by simp [hn]))
      exact ⟨finish, by simpa only [List.foldlM_cons, step, Option.bind_some] using execution, tail⟩

theorem walk_old (heap : Heap) (nodes : List Nat) (start : Nat) (path : Path heap start nodes) :
    ∃ finish, nodes.foldlM (oldStep heap) (some start) = some (some finish) := by
  induction nodes generalizing start with
  | nil => exact ⟨start, rfl⟩
  | cons node rest ih =>
      have step : oldStep heap (some start) node = some (some node) := by
        simp [oldStep, Concurrent.read, path.1, path.2.1, check]
      obtain ⟨finish, execution⟩ := ih node path.2.2
      exact ⟨finish, by simpa only [List.foldlM_cons, step, Option.bind_some] using execution⟩

theorem assertions_pass (heap : Heap) (head tail : Nat) (existing inserted order : List Nat)
    (perm : order.Perm inserted)
    (chain : Chain "next" "prev" heap none (head :: (order ++ existing ++ [tail])) none) :
    assertions heap head tail existing inserted = some () := by
  have path : Path heap head (order ++ (existing ++ [tail])) := by simpa [List.append_assoc] using chain.path
  obtain ⟨middle, first, remaining⟩ := walk_new heap inserted order (existing ++ [tail]) head path
    (fun _ member => perm.mem_iff.mp member)
  have first' : inserted.foldlM (fun current _ => newStep heap inserted current) (some head) = some (some middle) :=
    (fold_ignore_perm (newStep heap inserted) perm (some head)).symm.trans first
  obtain ⟨finish, last⟩ := walk_old heap (existing ++ [tail]) middle remaining
  have tail_next : heap tail "next" = none := Chain.tail_next (segment := head :: (order ++ existing)) (left := none) (by
    simpa only [List.cons_append] using chain)
  unfold assertions
  rw [first']
  dsimp only [Bind.bind, Option.bind]
  rw [last]
  simp [Concurrent.read, check, chain.1, tail_next]

end LinkedInsertion


namespace tests.py.parallel_doubly_linked_list

theorem insert_unsafe.«Not Concurrent(run_trial)» :
    ∃ (existing_count : Int) (insertion_count : Int) (_final : SharedState),
    ParallelRun.CanReturn (parallelRun (((List.range insertion_count.toNat).map (· + (((0 + 1) + 1) + existing_count.toNat))).map (fun _job => parallelFunction ParallelDoublyLinkedListAst.module "insert_unsafe" [.ref ((0)), .ref (_job), .lock 0])) (((([(0)] ++ (List.range existing_count.toNat).map (· + ((0 + 1) + 1)) ++ [((0 + 1))])).zip (((([(0)] ++ (List.range existing_count.toNat).map (· + ((0 + 1) + 1)) ++ [((0 + 1))])).drop 1))).foldl (fun _heap1 (_item2 : (Nat × Nat)) => Concurrent.putConcrete (Concurrent.putConcrete (_heap1) ((_item2).1) "next" (some ((_item2).2))) ((_item2).2) "prev" (some ((_item2).1))) (({ objects := List.replicate ((((0 + 1) + 1) + existing_count.toNat) + insertion_count.toNat) (.object [("prev", .none), ("next", .none)]) } : SharedState)))) _final ∧
    ((do let _local3 := some ((0)); let _result8 ← ((List.range insertion_count.toNat).map (· + (((0 + 1) + 1) + existing_count.toNat))).foldlM (fun _state4 (_item5 : Nat) => do let _local6 := (← Concurrent.readConcrete _final (_state4) "next"); Concurrent.check ((((List.range insertion_count.toNat).map (· + (((0 + 1) + 1) + existing_count.toNat))).map some).contains (_local6)); Concurrent.check (((← Concurrent.readConcrete _final (_local6) "prev")) == (_state4)); let _local7 := _local6; pure _local7) (_local3); let _result12 ← (((List.range existing_count.toNat).map (· + ((0 + 1) + 1)) ++ [((0 + 1))])).foldlM (fun _state9 (_item10 : Nat) => do Concurrent.check (((← Concurrent.readConcrete _final (_state9) "next")) == (some (_item10))); Concurrent.check (((← Concurrent.readConcrete _final (some (_item10)) "prev")) == (_state9)); let _local11 := some (_item10); pure _local11) (_result8); Concurrent.check (((← Concurrent.readConcrete _final (some ((0))) "prev")) == (none)); Concurrent.check (((← Concurrent.readConcrete _final (some (((0 + 1)))) "next")) == (none)); pure ()) : Option Unit) = none
  := by
  let broken : SharedState := { objects := [
    .object [("prev", .none), ("next", .ref 3)],
    .object [("prev", .ref 2), ("next", .none)],
    .object [("prev", .ref 0), ("next", .ref 1)],
    .object [("prev", .ref 0), ("next", .ref 1)]] }
  refine ⟨0, 2, broken, ?_, ?_⟩
  · native_decide
  · decide

theorem insert_safe.«Concurrent(run_trial)» :
    ∀ (existing_count : Int) (insertion_count : Int) (head : Nat) (tail : Nat) (existing : List Nat) (inserted : List Nat),
    ([head, tail] ++ existing ++ inserted).Nodup →
    existing.length = existing_count.toNat →
    inserted.length = insertion_count.toNat →
    Concurrent.Ensures ParallelDoublyLinkedListAst.module "insert_safe"
    ["head", "node"] "mutex" (fun _job => [some (head), some (_job)])
    (inserted) (((([head] ++ existing ++ [tail])).zip (((([head] ++ existing ++ [tail])).drop 1))).foldl (fun _heap1 (_item2 : (Nat × Nat)) => Concurrent.put (Concurrent.put (_heap1) ((_item2).1) "next" (some ((_item2).2))) ((_item2).2) "prev" (some ((_item2).1))) ((fun (_ : Nat) (_ : String) => (none : Option Nat)))) (fun _final => ((do let _local3 := some (head); let _result8 ← (inserted).foldlM (fun _state4 (_item5 : Nat) => do let _local6 := (← Concurrent.read _final (_state4) "next"); Concurrent.check (((inserted).map some).contains (_local6)); Concurrent.check (((← Concurrent.read _final (_local6) "prev")) == (_state4)); let _local7 := _local6; pure _local7) (_local3); let _result12 ← ((existing ++ [tail])).foldlM (fun _state9 (_item10 : Nat) => do Concurrent.check (((← Concurrent.read _final (_state9) "next")) == (some (_item10))); Concurrent.check (((← Concurrent.read _final (some (_item10)) "prev")) == (_state9)); let _local11 := some (_item10); pure _local11) (_result8); Concurrent.check (((← Concurrent.read _final (some (head)) "prev")) == (none)); Concurrent.check (((← Concurrent.read _final (some (tail)) "next")) == (none)); pure ()) : Option Unit) = some ())
  := by
  intro existing_count insertion_count head tail existing inserted distinct _ _
  refine ⟨LinkedInsertion.ops, ?_, ?_⟩
  · decide
  · change LockedEnsures (LinkedInsertion.program head)
      (fun final => LinkedInsertion.assertions final head tail existing inserted = some ())
      inserted none (LinkedInsertion.wire (fun _ _ => none) (head :: (existing ++ [tail])))
    have reordered : (head :: (inserted ++ existing ++ [tail])).Nodup := by
      simp only [List.nodup_cons, List.nodup_append, List.mem_append,
        List.mem_cons, List.not_mem_nil, not_false_eq_true, or_false, not_or] at distinct ⊢
      grind
    have startDistinct : (head :: (existing ++ [tail])).Nodup := by
      simp only [List.nodup_cons, List.nodup_append, List.mem_append,
        List.mem_cons, List.not_mem_nil, not_false_eq_true, or_false, not_or] at distinct ⊢
      grind
    apply LockedEnsures.mono _ (LinkedInsertion.all_insertions head tail existing inserted _ reordered
      (LinkedInsertion.wire_chain _ _ none startDistinct (by intros; rfl) (by intros; rfl) (by intros; rfl)))
    intro final h
    obtain ⟨order, perm, _, chain⟩ := h
    exact LinkedInsertion.assertions_pass final head tail existing inserted order perm chain

end tests.py.parallel_doubly_linked_list
