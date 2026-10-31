import lang.py.FormalSW.MachineDictionaryIteration

/-! Positional iterators snapshot their pool and allocate tuples as rows are consumed. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- The common pool read excludes user-defined iteration protocols. -/
def positionalPool (source : Value) : Mutable.Eval (List Value) := fun heap =>
  match source with
  | .ref address => match heap[address]? with
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => none
      | _ => Mutable.sequence source heap
  | .scalar _ => Mutable.sequence source heap

theorem positionalPool_keeps_heap (heap : Mutable.Heap) (source : Value)
    (outcome : Except ExceptionObject (List Value)) (after : Mutable.Heap)
    (executed : positionalPool source heap = some (outcome, after)) : after = heap := by
  cases source with
  | scalar value => exact sequence_keeps_heap heap after (.scalar value) outcome executed
  | ref address =>
    cases found : heap[address]? with
    | none => exact sequence_keeps_heap heap after (.ref address) outcome (by simpa [positionalPool, found] using executed)
    | some object =>
      cases object <;> simp only [positionalPool, found] at executed <;> try contradiction
      all_goals exact sequence_keeps_heap heap after (.ref address) outcome executed

theorem positionalPool_sequence (heap : Mutable.Heap) (source : Value) (items : List Value)
    (executed : positionalPool source heap = some (.ok items, heap)) :
    Mutable.sequence source heap = some (.ok items, heap) := by
  cases source with
  | scalar value => exact executed
  | ref address =>
    cases found : heap[address]? with
    | none => simpa [positionalPool, found] using executed
    | some object =>
      cases object <;> simp only [positionalPool, found] at executed
      all_goals first | contradiction | exact executed

theorem positionalPool_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (source : Value) (inside : source.edge.Within logical.length) :
    positionalPool (relocateValue rename source) physical =
      (positionalPool source logical).map (fun pair => (pair.1.map (List.map (relocateValue rename)), physical)) := by
  cases source with
  | scalar value => exact layout.sequence (.scalar value) inside
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;>
      simp only [positionalPool, relocateValue, moved, found, object, relocateObject]
    all_goals first | rfl | exact layout.sequence (.ref address) inside

theorem permutation_acquire_pool (source length : Value) :
    Permutations.acquire source length = (do
      let pool ← positionalPool source
      let count ← Permutations.size pool.length length
      pure ⟨Permutations.rows count pool⟩) := by
  funext heap
  cases source with
  | scalar value => simp [Permutations.acquire, positionalPool, Mutable.eval_bind]
  | ref address =>
    cases found : heap[address]? with
    | none => simp [Permutations.acquire, positionalPool, found, Mutable.eval_bind]
    | some object => cases object <;> simp [Permutations.acquire, positionalPool, found, Mutable.eval_bind, Mutable.unsupported]

theorem combination_acquire_pool (source length : Value) :
    Combinations.acquire source length = (do
      let pool ← positionalPool source
      match length with
      | .scalar .none => Mutable.error "TypeError"
      | _ => do
          let count ← Permutations.size pool.length length
          pure ⟨Combinations.rows count pool⟩) := by
  funext heap
  cases source with
  | scalar value =>
    simp [Combinations.acquire, positionalPool, Mutable.eval_bind] <;> cases length <;> try rfl
    all_goals rename_i value; cases value <;> rfl
  | ref address =>
    cases found : heap[address]? with
    | none =>
      simp [Combinations.acquire, positionalPool, found, Mutable.eval_bind] <;> cases length <;> try rfl
      all_goals rename_i value; cases value <;> rfl
    | some object =>
      cases object <;> simp [Combinations.acquire, positionalPool, found, Mutable.eval_bind, Mutable.unsupported]
      all_goals cases length <;> try rfl
      all_goals rename_i value; cases value <;> rfl

theorem positionalSize_keeps_heap (heap : Mutable.Heap) (poolLength : Nat) (length : Value)
    (outcome : Except ExceptionObject Nat) (after : Mutable.Heap)
    (executed : Permutations.size poolLength length heap = some (outcome, after)) : after = heap := by
  cases length with
  | ref address => simpa [Permutations.size, Mutable.error] using (congrArg (Option.map Prod.snd) executed).symm
  | scalar value =>
    cases value <;> simp only [Permutations.size] at executed
    all_goals first
      | simpa [Mutable.error] using (congrArg (Option.map Prod.snd) executed).symm
      | (split at executed <;> simpa [Mutable.error] using (congrArg (Option.map Prod.snd) executed).symm)

theorem positionalSize_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat) (poolLength : Nat) (length : Value) :
    Permutations.size poolLength (relocateValue rename length) physical =
      (Permutations.size poolLength length logical).map (fun pair => (pair.1, physical)) := by
  cases length with
  | ref address => rfl
  | scalar value =>
    cases value <;> simp only [relocateValue, Permutations.size]
    all_goals first | rfl | (split <;> rfl)

def relocateCursor (rename : Nat → Nat) (cursor : Permutations.Cursor) : Permutations.Cursor :=
  ⟨cursor.remaining.map (List.map (relocateValue rename))⟩

theorem permutation_acquire_keeps_heap (heap : Mutable.Heap) (source length : Value)
    (outcome : Except ExceptionObject Permutations.Cursor) (after : Mutable.Heap)
    (executed : Permutations.acquire source length heap = some (outcome, after)) : after = heap := by
  rw [permutation_acquire_pool] at executed
  apply readonly_bind_keeps_heap heap _ _ (fun result middle read => positionalPool_keeps_heap heap source result middle read)
    _ outcome after executed
  intro pool read result middle continued
  apply readonly_bind_keeps_heap heap _ _ (fun result middle read => positionalSize_keeps_heap heap pool.length length result middle read)
    _ result middle continued
  intro count converted result final returned
  simpa using (congrArg (Option.map Prod.snd) returned).symm

theorem permutation_acquire_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (source length : Value) (inside : source.edge.Within logical.length) :
    Permutations.acquire (relocateValue rename source) (relocateValue rename length) physical =
      (Permutations.acquire source length logical).map (fun pair => (pair.1.map (relocateCursor rename), physical)) := by
  rw [permutation_acquire_pool, permutation_acquire_pool]
  apply readonly_bind_relocates logical physical _ _ (List.map (relocateValue rename)) _ _ _
    (fun result middle read => positionalPool_keeps_heap logical source result middle read) (positionalPool_relocates layout source inside)
  intro pool read
  simp only [List.length_map]
  apply readonly_bind_relocates logical physical _ _ id _ _ _
    (fun result middle converted => positionalSize_keeps_heap logical pool.length length result middle converted)
    (by simpa only [Except.map_id] using positionalSize_relocates logical physical rename pool.length length)
  intro count converted
  simp [relocateCursor, Permutations.rows_map, Except.map]

theorem combination_acquire_keeps_heap (heap : Mutable.Heap) (source length : Value)
    (outcome : Except ExceptionObject Permutations.Cursor) (after : Mutable.Heap)
    (executed : Combinations.acquire source length heap = some (outcome, after)) : after = heap := by
  rw [combination_acquire_pool] at executed
  apply readonly_bind_keeps_heap heap _ _ (fun result middle read => positionalPool_keeps_heap heap source result middle read)
    _ outcome after executed
  intro pool read result middle continued
  have sized (length : Value) (completed : (do
      let count ← Permutations.size pool.length length
      pure (⟨Combinations.rows count pool⟩ : Permutations.Cursor)) heap = some (result, middle)) : middle = heap := by
    apply readonly_bind_keeps_heap heap _ _ (fun result middle read => positionalSize_keeps_heap heap pool.length length result middle read)
      _ result middle completed
    intro count converted result final returned
    simpa using (congrArg (Option.map Prod.snd) returned).symm
  cases length with
  | ref address => exact sized (.ref address) continued
  | scalar value =>
    cases value <;> first
      | exact sized _ continued
      | simpa [Mutable.error] using (congrArg (Option.map Prod.snd) continued).symm

theorem combination_acquire_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (source length : Value) (inside : source.edge.Within logical.length) :
    Combinations.acquire (relocateValue rename source) (relocateValue rename length) physical =
      (Combinations.acquire source length logical).map (fun pair => (pair.1.map (relocateCursor rename), physical)) := by
  rw [combination_acquire_pool, combination_acquire_pool]
  apply readonly_bind_relocates logical physical _ _ (List.map (relocateValue rename)) _ _ _
    (fun result middle read => positionalPool_keeps_heap logical source result middle read) (positionalPool_relocates layout source inside)
  intro pool read
  have sized (length : Value) :
      (do let count ← Permutations.size pool.length (relocateValue rename length)
          pure (⟨Combinations.rows count (pool.map (relocateValue rename))⟩ : Permutations.Cursor)) physical =
        ((do let count ← Permutations.size pool.length length
             pure (⟨Combinations.rows count pool⟩ : Permutations.Cursor)) logical).map
          (fun pair : Except ExceptionObject Permutations.Cursor × Mutable.Heap =>
            (pair.1.map (relocateCursor rename), physical)) := by
    apply readonly_bind_relocates logical physical _ _ id _ _ _
      (fun result middle converted => positionalSize_keeps_heap logical pool.length length result middle converted)
      (by simpa only [Except.map_id] using positionalSize_relocates logical physical rename pool.length length)
    intro count converted
    simp [relocateCursor, Combinations.rows_map, Except.map]
  cases length with
  | ref address => simpa only [relocateValue, List.length_map] using sized (.ref address)
  | scalar value =>
    cases value with
    | int number => simpa only [relocateValue, List.length_map] using sized (.scalar (.int number))
    | bool flag => simpa only [relocateValue, List.length_map] using sized (.scalar (.bool flag))
    | _ => rfl

theorem permutation_row_mem {α : Type} (count : Nat) (pool row : List α)
    (selected : row ∈ Permutations.rows count pool) : ∀ value ∈ row, value ∈ pool := by
  induction count generalizing pool row with
  | zero =>
    have empty : row = [] := by simpa [Permutations.rows] using selected
    simp [empty]
  | succ count ih =>
    simp only [Permutations.rows, List.mem_flatMap, List.mem_map] at selected
    obtain ⟨⟨first, rest⟩, chosen, tail, member, rfl⟩ := selected
    intro value present
    apply (Permutations.choice_perm chosen).mem_iff.mp
    rcases List.mem_cons.mp present with rfl | present
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih rest tail member value present)

theorem permutation_acquire_rows (heap : Mutable.Heap) (source length : Value) (cursor : Permutations.Cursor)
    (executed : Permutations.acquire source length heap = some (.ok cursor, heap)) :
    ∃ pool count, positionalPool source heap = some (.ok pool, heap) ∧ cursor.remaining = Permutations.rows count pool := by
  rw [permutation_acquire_pool] at executed
  obtain ⟨pool, read, continued⟩ := readonly_bind_success heap _ _
    (fun result middle read => positionalPool_keeps_heap heap source result middle read) cursor heap executed
  obtain ⟨count, _, returned⟩ := readonly_bind_success heap _ _
    (fun result middle read => positionalSize_keeps_heap heap pool.length length result middle read) cursor heap continued
  have same : cursor = ⟨Permutations.rows count pool⟩ := by simpa using returned.symm
  exact ⟨pool, count, read, congrArg Permutations.Cursor.remaining same⟩

theorem combination_acquire_rows (heap : Mutable.Heap) (source length : Value) (cursor : Permutations.Cursor)
    (executed : Combinations.acquire source length heap = some (.ok cursor, heap)) :
    ∃ pool count, positionalPool source heap = some (.ok pool, heap) ∧ cursor.remaining = Combinations.rows count pool := by
  rw [combination_acquire_pool] at executed
  obtain ⟨pool, read, continued⟩ := readonly_bind_success heap _ _
    (fun result middle read => positionalPool_keeps_heap heap source result middle read) cursor heap executed
  have sized (length : Value) (completed : (do
      let count ← Permutations.size pool.length length
      pure (⟨Combinations.rows count pool⟩ : Permutations.Cursor)) heap = some (.ok cursor, heap)) :
      ∃ pool count, positionalPool source heap = some (.ok pool, heap) ∧ cursor.remaining = Combinations.rows count pool := by
    obtain ⟨count, _, returned⟩ := readonly_bind_success heap _ _
      (fun result middle read => positionalSize_keeps_heap heap pool.length length result middle read) cursor heap completed
    have same : cursor = ⟨Combinations.rows count pool⟩ := by simpa using returned.symm
    exact ⟨pool, count, read, congrArg Permutations.Cursor.remaining same⟩
  cases length with
  | ref address => exact sized (.ref address) continued
  | scalar value =>
    cases value <;> first | exact sized _ continued | simp [Mutable.error] at continued

theorem permutation_acquire_within (heap : Mutable.Heap) (closed : Closed heap) (source length : Value)
    (cursor : Permutations.Cursor) (executed : Permutations.acquire source length heap = some (.ok cursor, heap)) :
    ∀ row ∈ cursor.remaining, ∀ value ∈ row, value.edge.Within heap.length := by
  obtain ⟨pool, count, read, rows⟩ := permutation_acquire_rows heap source length cursor executed
  intro row member value present
  rw [rows] at member
  apply sequence_items_within heap heap closed source pool (positionalPool_sequence heap source pool read) value
  exact permutation_row_mem count pool row member value present

theorem combination_acquire_within (heap : Mutable.Heap) (closed : Closed heap) (source length : Value)
    (cursor : Permutations.Cursor) (executed : Combinations.acquire source length heap = some (.ok cursor, heap)) :
    ∀ row ∈ cursor.remaining, ∀ value ∈ row, value.edge.Within heap.length := by
  obtain ⟨pool, count, read, rows⟩ := combination_acquire_rows heap source length cursor executed
  intro row member value present
  rw [rows] at member
  apply sequence_items_within heap heap closed source pool (positionalPool_sequence heap source pool read) value
  exact (Combinations.mem_rows_iff count pool row).mp member |>.1.subset present

theorem permutationRows_keeps_heap (heap : Mutable.Heap) (values : List Value)
    (outcome : Except ExceptionObject (List (List SequenceSource))) (after : Mutable.Heap)
    (executed : permutationRows values heap = some (outcome, after)) : after = heap := by
  cases values with
  | nil => simpa [permutationRows, Mutable.error] using (congrArg (Option.map Prod.snd) executed).symm
  | cons source rest =>
    cases rest with
    | nil => simpa [permutationRows, Mutable.error] using (congrArg (Option.map Prod.snd) executed).symm
    | cons length rest =>
      cases rest with
      | cons extra rest => simpa [permutationRows, Mutable.error] using (congrArg (Option.map Prod.snd) executed).symm
      | nil =>
        apply readonly_bind_keeps_heap heap _ _
          (fun result middle read => permutation_acquire_keeps_heap heap source length result middle read) _ outcome after executed
        intro cursor read result final returned
        simpa using (congrArg (Option.map Prod.snd) returned).symm

theorem permutationRows_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (values : List Value)
    (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    permutationRows (values.map (relocateValue rename)) physical =
      (permutationRows values logical).map
        (fun pair => (pair.1.map (List.map (List.map (relocateSource rename))), physical)) := by
  cases values with
  | nil => rfl
  | cons source rest =>
    cases rest with
    | nil => rfl
    | cons length rest =>
      cases rest with
      | cons extra rest => rfl
      | nil =>
        apply readonly_bind_relocates logical physical _ _ (relocateCursor rename) _ _ _
          (fun result middle read => permutation_acquire_keeps_heap logical source length result middle read)
          (permutation_acquire_relocates layout source length (inside source (by simp)))
        intro cursor read
        simp [relocateCursor, List.map_map, Function.comp_def, sequenceSource_relocate, Except.map]

theorem permutationRows_within (heap : Mutable.Heap) (closed : Closed heap) (values : List Value)
    (rows : List (List SequenceSource)) (executed : permutationRows values heap = some (.ok rows, heap)) :
    ∀ row ∈ rows, ∀ source ∈ row, SourceWithin heap.length source := by
  cases values with
  | nil => simp [permutationRows, Mutable.error] at executed
  | cons source rest =>
    cases rest with
    | nil => simp [permutationRows, Mutable.error] at executed
    | cons length rest =>
      cases rest with
      | cons extra rest => simp [permutationRows, Mutable.error] at executed
      | nil =>
        obtain ⟨cursor, read, returned⟩ := readonly_bind_success heap _ _
          (fun result middle read => permutation_acquire_keeps_heap heap source length result middle read) rows heap executed
        have same : rows = cursor.remaining.map (List.map sequenceSource) := by simpa using returned.symm
        rw [same]
        intro row member value present
        obtain ⟨items, selected, rfl⟩ := List.mem_map.mp member
        obtain ⟨item, member, rfl⟩ := List.mem_map.mp present
        exact sequenceSource_within heap.length item (permutation_acquire_within heap closed source length cursor read items selected item member)

theorem combinationRows_keeps_heap (heap : Mutable.Heap) (values : List Value)
    (outcome : Except ExceptionObject (List (List SequenceSource))) (after : Mutable.Heap)
    (executed : combinationRows values heap = some (outcome, after)) : after = heap := by
  cases values with
  | nil => simpa [combinationRows, Mutable.error] using (congrArg (Option.map Prod.snd) executed).symm
  | cons source rest =>
    cases rest with
    | nil => simpa [combinationRows, Mutable.error] using (congrArg (Option.map Prod.snd) executed).symm
    | cons length rest =>
      cases rest with
      | cons extra rest => simpa [combinationRows, Mutable.error] using (congrArg (Option.map Prod.snd) executed).symm
      | nil =>
        apply readonly_bind_keeps_heap heap _ _
          (fun result middle read => combination_acquire_keeps_heap heap source length result middle read) _ outcome after executed
        intro cursor read result final returned
        simpa using (congrArg (Option.map Prod.snd) returned).symm

theorem combinationRows_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (values : List Value)
    (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    combinationRows (values.map (relocateValue rename)) physical =
      (combinationRows values logical).map
        (fun pair => (pair.1.map (List.map (List.map (relocateSource rename))), physical)) := by
  cases values with
  | nil => rfl
  | cons source rest =>
    cases rest with
    | nil => rfl
    | cons length rest =>
      cases rest with
      | cons extra rest => rfl
      | nil =>
        apply readonly_bind_relocates logical physical _ _ (relocateCursor rename) _ _ _
          (fun result middle read => combination_acquire_keeps_heap logical source length result middle read)
          (combination_acquire_relocates layout source length (inside source (by simp)))
        intro cursor read
        simp [relocateCursor, List.map_map, Function.comp_def, sequenceSource_relocate, Except.map]

theorem combinationRows_within (heap : Mutable.Heap) (closed : Closed heap) (values : List Value)
    (rows : List (List SequenceSource)) (executed : combinationRows values heap = some (.ok rows, heap)) :
    ∀ row ∈ rows, ∀ source ∈ row, SourceWithin heap.length source := by
  cases values with
  | nil => simp [combinationRows, Mutable.error] at executed
  | cons source rest =>
    cases rest with
    | nil => simp [combinationRows, Mutable.error] at executed
    | cons length rest =>
      cases rest with
      | cons extra rest => simp [combinationRows, Mutable.error] at executed
      | nil =>
        obtain ⟨cursor, read, returned⟩ := readonly_bind_success heap _ _
          (fun result middle read => combination_acquire_keeps_heap heap source length result middle read) rows heap executed
        have same : rows = cursor.remaining.map (List.map sequenceSource) := by simpa using returned.symm
        rw [same]
        intro row member value present
        obtain ⟨items, selected, rfl⟩ := List.mem_map.mp member
        obtain ⟨item, member, rfl⟩ := List.mem_map.mp present
        exact sequenceSource_within heap.length item (combination_acquire_within heap closed source length cursor read items selected item member)

end FormalSW.PyAst.HeapCalls.Relocation
