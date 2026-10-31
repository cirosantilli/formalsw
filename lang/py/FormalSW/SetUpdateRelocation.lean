import lang.py.FormalSW.SetConstructionEffects

/-! Multi-source updates preserve shared keys, partial mutations, and heap layouts. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

variable {logical physical : Heap} {rename : Nat → Nat}

/-- Each source sees the heap left by the previous source, including when they alias the receiver. -/
theorem ExecutionLayout.updateSet (sources : List Value) (layout : ExecutionLayout logical physical rename)
    (address : Nat) (addressInside : address < logical.length)
    (inside : ∀ source ∈ sources, source.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.updateSet address sources logical = some (outcome, after)) :
    ∃ other,
      Mutable.updateSet (rename address) (sources.map (relocateValue rename)) physical =
        some (outcome.map (relocateValue rename), other) ∧
      ExecutionLayout after other rename ∧ after.length = logical.length ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  induction sources generalizing logical physical outcome after with
  | nil =>
    have same : some (.ok (.scalar .none), logical) = some (outcome, after) := executed
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
    refine ⟨physical, rfl, layout, rfl, ?_⟩
    intro returned equal
    cases equal
    trivial
  | cons source rest ih =>
    have sourceInside := inside source (List.mem_cons_self ..)
    have sourceSame := layout.runtime.setSourceItems source sourceInside
    cases read : setSourceItems source logical with
    | none => simp [Mutable.updateSet, read, eval_bind] at executed
    | some pair =>
      rcases pair with ⟨result, middle⟩
      have unchanged := setSourceItems_keeps_heap logical middle source sourceInside result read
      subst middle
      cases result with
      | error exception =>
        have same : some (.error exception, logical) = some (outcome, after) := by
          simpa [Mutable.updateSet, read, eval_bind] using executed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        refine ⟨physical, ?_, layout, rfl, ?_⟩
        · simp [Mutable.updateSet, sourceSame, read, eval_bind, Except.map]
        · intro returned impossible; cases impossible
      | ok items =>
        cases inserted : items.mapM (Mutable.addItem address) logical with
        | none => simp [Mutable.updateSet, read, inserted, eval_bind] at executed
        | some pair =>
          rcases pair with ⟨result, middle⟩
          obtain ⟨otherMiddle, otherInserted, middleLayout, sameLength⟩ := layout.addItems items address addressInside
            (setSourceItems_bounded logical layout.closed source sourceInside items read) result middle inserted
          cases result with
          | error exception =>
            have same : some (.error exception, middle) = some (outcome, after) := by
              simpa [Mutable.updateSet, read, inserted, eval_bind] using executed
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
            refine ⟨otherMiddle, ?_, middleLayout, sameLength, ?_⟩
            · simp [Mutable.updateSet, sourceSame, read, otherInserted, eval_bind, Except.map]
            · intro returned impossible; cases impossible
          | ok ignored =>
            have continued : Mutable.updateSet address rest middle = some (outcome, after) := by
              simpa [Mutable.updateSet, read, inserted, eval_bind] using executed
            obtain ⟨other, otherRest, finalLayout, finalLength, bounded⟩ := ih middleLayout
              (by simpa [sameLength] using addressInside)
              (fun value member => by simpa [sameLength] using inside value (List.mem_cons_of_mem _ member))
              outcome after continued
            refine ⟨other, ?_, finalLayout, finalLength.trans sameLength, bounded⟩
            simpa [Mutable.updateSet, sourceSame, read, otherInserted, eval_bind, Except.map] using otherRest

/-- Relocation also preserves unsupported sources and unsupported hashing after partial updates. -/
theorem ExecutionLayout.updateSet_unsupported (sources : List Value)
    (layout : ExecutionLayout logical physical rename) (address : Nat) (addressInside : address < logical.length)
    (inside : ∀ source ∈ sources, source.edge.Within logical.length) :
    Mutable.updateSet (rename address) (sources.map (relocateValue rename)) physical = none ↔
      Mutable.updateSet address sources logical = none := by
  induction sources generalizing logical physical with
  | nil => simp [Mutable.updateSet]
  | cons source rest ih =>
    have sourceInside := inside source (List.mem_cons_self ..)
    have sourceSame := layout.runtime.setSourceItems source sourceInside
    cases read : setSourceItems source logical with
    | none => simp [Mutable.updateSet, sourceSame, read, eval_bind]
    | some pair =>
      rcases pair with ⟨result, middle⟩
      have unchanged := setSourceItems_keeps_heap logical middle source sourceInside result read
      subst middle
      cases result with
      | error exception => simp [Mutable.updateSet, sourceSame, read, eval_bind, Except.map]
      | ok items =>
        have itemsInside := setSourceItems_bounded logical layout.closed source sourceInside items read
        have unsupported := layout.addItems_unsupported items address addressInside itemsInside
        cases inserted : items.mapM (Mutable.addItem address) logical with
        | none =>
          have other := unsupported.mpr inserted
          simp [Mutable.updateSet, sourceSame, read, inserted, other, eval_bind, Except.map]
        | some pair =>
          rcases pair with ⟨result, middle⟩
          obtain ⟨otherMiddle, otherInserted, middleLayout, sameLength⟩ :=
            layout.addItems items address addressInside itemsInside result middle inserted
          cases result with
          | error exception => simp [Mutable.updateSet, sourceSame, read, inserted, otherInserted, eval_bind, Except.map]
          | ok ignored =>
            have remaining := ih middleLayout (by simpa [sameLength] using addressInside)
              (fun value member => by simpa [sameLength] using inside value (List.mem_cons_of_mem _ member))
            simpa [Mutable.updateSet, sourceSame, read, inserted, otherInserted, eval_bind, Except.map] using remaining

theorem HeapGrows.setSourceItems (source : Value) : HeapGrows (Mutable.setSourceItems source) := by
  unfold Mutable.setSourceItems
  with_reducible repeat' first
    | exact HeapGrows.sequence _
    | exact HeapGrows.pure _
    | exact HeapGrows.unsupported
    | apply HeapGrows.bind HeapGrows.get; intro heap
    | split

theorem HeapGrows.updateSet (address : Nat) (sources : List Value) : HeapGrows (Mutable.updateSet address sources) := by
  induction sources with
  | nil => exact HeapGrows.pure _
  | cons source rest ih =>
    unfold Mutable.updateSet
    apply HeapGrows.bind (HeapGrows.setSourceItems source)
    intro items
    apply HeapGrows.bind (HeapGrows.mapM items (Mutable.addItem address) (fun item _ => HeapGrows.addItem address item))
    intro ignored
    exact ih

end FormalSW.PyAst.Mutable.Relocation
