import lang.py.FormalSW.ItemWriteRelocation
import lang.py.FormalSW.DictionaryConstructor
import lang.py.FormalSW.ConstructionRelocation

/-! Dictionary rows preserve partial insertions, key representatives and errors. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

variable {logical physical : Heap} {rename : Nat → Nat}

theorem RuntimeLayout.dictionaryIterable (layout : RuntimeLayout logical physical rename)
    (source : Value) (inside : source.edge.Within logical.length) :
    DictionaryConstructor.iterable (relocateValue rename source) physical =
      (DictionaryConstructor.iterable source logical).map
        (fun result => (result.1.map (List.map (relocateValue rename)), physical)) := by
  cases source with
  | scalar scalar =>
    cases scalar <;> simp [DictionaryConstructor.iterable, Mutable.sequence, relocateValue, error, Except.map,
      List.map_map, Function.comp_def]
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;>
      simp only [object, relocateObject] at moved <;>
      simp [DictionaryConstructor.iterable, Mutable.sequence, relocateValue, found, object, moved, unsupported,
        Except.map, List.map_map, Function.comp_def]

theorem dictionaryIterable_heap (heap after : Heap) (source : Value)
    (inside : source.edge.Within heap.length) (outcome : Except ExceptionObject (List Value))
    (executed : DictionaryConstructor.iterable source heap = some (outcome, after)) : after = heap := by
  have same := (RuntimeLayout.refl heap).dictionaryIterable source inside
  simp only [relocateValue_id, executed, Option.map_some] at same
  exact congrArg Prod.snd (Option.some.inj same)

theorem dictionaryIterable_bounded (heap : Heap) (closed : Closed heap) (source : Value)
    (inside : source.edge.Within heap.length) (items : List Value)
    (executed : DictionaryConstructor.iterable source heap = some (.ok items, heap)) :
    ∀ value ∈ items, value.edge.Within heap.length := by
  cases source with
  | scalar scalar =>
    cases scalar with
    | int value | bool value | none => simp [DictionaryConstructor.iterable, Mutable.sequence, error] at executed
    | string text | bytes bytes =>
      simp [DictionaryConstructor.iterable, Mutable.sequence] at executed
      subst items
      intro value member
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      trivial
  | ref address =>
    have found : heap[address]? = some heap[address] := List.getElem?_eq_getElem inside
    generalize objectValue : heap[address] = object at found
    have old := closed object (List.mem_of_getElem? found)
    cases object with
    | list values | tuple values =>
      simp [DictionaryConstructor.iterable, Mutable.sequence, found] at executed
      subst items
      exact old
    | bytearray bytes | dict entries =>
      simp [DictionaryConstructor.iterable, Mutable.sequence, found] at executed
      subst items
      intro value member
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      trivial
    | keyDict entries =>
      simp [DictionaryConstructor.iterable, found] at executed
      subst items
      intro value member
      obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
      exact old entry.2.1 (List.mem_flatMap.mpr ⟨entry, present, by simp⟩)
    | set values | keySet entries | «instance» origin name fields | dataInstance origin name frozen declared fields =>
      simp [DictionaryConstructor.iterable, found, unsupported] at executed

/-- A pair of evaluations retains both partial heaps, or agrees on unsupported execution. -/
def UnitMutationPair (logical physical : Heap) (rename : Nat → Nat) (left right : Eval Unit) : Prop :=
  ∃ outcome : Option (Except ExceptionObject Unit), ∃ after other,
    left logical = outcome.map (fun result => (result, after)) ∧
    right physical = outcome.map (fun result => (result, other)) ∧
    ExecutionLayout after other rename ∧ after.length = logical.length ∧ other.length = physical.length

theorem ExecutionLayout.dictionaryInsertRow (layout : ExecutionLayout logical physical rename)
    (address : Nat) (row : Value) (addressInside : address < logical.length) (rowInside : row.edge.Within logical.length) :
    UnitMutationPair logical physical rename (DictionaryConstructor.insertRow address row)
      (DictionaryConstructor.insertRow (rename address) (relocateValue rename row)) := by
  have paired := layout.runtime.dictionaryIterable row rowInside
  cases read : DictionaryConstructor.iterable row logical with
  | none =>
    exact ⟨none, logical, physical, by simp [DictionaryConstructor.insertRow, eval_bind, read],
      by simp [DictionaryConstructor.insertRow, eval_bind, paired, read], layout, rfl, rfl⟩
  | some pair =>
    rcases pair with ⟨result, middle⟩
    have same := dictionaryIterable_heap logical middle row rowInside result read
    subst middle
    cases result with
    | error exception =>
      exact ⟨some (.error exception), logical, physical, by simp [DictionaryConstructor.insertRow, eval_bind, read],
        by simp [DictionaryConstructor.insertRow, eval_bind, paired, read, Except.map], layout, rfl, rfl⟩
    | ok items =>
      have bounded := dictionaryIterable_bounded logical layout.closed row rowInside items read
      rcases items with _ | ⟨key, _ | ⟨value, _ | ⟨extra, rest⟩⟩⟩
      case cons.cons.nil =>
        have keyInside := bounded key (by simp)
        have valueInside := bounded value (by simp)
        cases write : Mutable.setItem (.ref address) key value logical with
        | none =>
          have moved := (layout.runtime.setItem_unsupported layout.closed (.ref address) key value addressInside keyInside).mpr write
          change Mutable.setItem (.ref (rename address)) (relocateValue rename key) (relocateValue rename value) physical = none at moved
          exact ⟨none, logical, physical, by simp [DictionaryConstructor.insertRow, eval_bind, read, write],
            by simp [DictionaryConstructor.insertRow, eval_bind, paired, read, moved, Except.map], layout, rfl, rfl⟩
        | some pair =>
          rcases pair with ⟨outcome, after⟩
          obtain ⟨other, moved, retained⟩ := layout.setItem (.ref address) key value addressInside keyInside valueInside outcome after write
          change Mutable.setItem (.ref (rename address)) (relocateValue rename key) (relocateValue rename value) physical = some (outcome.map (relocateValue rename), other) at moved
          have effect := setItem_effect logical after (.ref address) key value outcome write
          have otherEffect := setItem_effect physical other (.ref (rename address)) (relocateValue rename key) (relocateValue rename value) _ moved
          refine ⟨some (outcome.map (fun _ => ())), after, other, ?_, ?_, retained, effect.1, otherEffect.1⟩
          · cases outcome <;> simp [DictionaryConstructor.insertRow, eval_bind, read, write, Except.map]
          · cases outcome <;> simp [DictionaryConstructor.insertRow, eval_bind, paired, read, moved, Except.map]
      all_goals
        exact ⟨some (.error ⟨"ValueError", []⟩), logical, physical,
          by simp [DictionaryConstructor.insertRow, eval_bind, read, error],
          by simp [DictionaryConstructor.insertRow, eval_bind, paired, read, Except.map, error], layout, rfl, rfl⟩

theorem ExecutionLayout.dictionaryInsertRows (layout : ExecutionLayout logical physical rename)
    (address : Nat) (rows : List Value) (addressInside : address < logical.length)
    (rowsInside : ∀ row ∈ rows, row.edge.Within logical.length) :
    UnitMutationPair logical physical rename (DictionaryConstructor.insertRows address rows)
      (DictionaryConstructor.insertRows (rename address) (rows.map (relocateValue rename))) := by
  induction rows generalizing logical physical with
  | nil => exact ⟨some (.ok ()), logical, physical, rfl, rfl, layout, rfl, rfl⟩
  | cons row rest ih =>
    obtain ⟨outcome, middle, otherMiddle, first, otherFirst, retained, size, otherSize⟩ :=
      layout.dictionaryInsertRow address row addressInside (rowsInside row (by simp))
    cases outcome with
    | none =>
      exact ⟨none, logical, physical, by simp [DictionaryConstructor.insertRows, eval_bind, first],
        by simp [DictionaryConstructor.insertRows, eval_bind, otherFirst], layout, rfl, rfl⟩
    | some result =>
      cases result with
      | error exception =>
        exact ⟨some (.error exception), middle, otherMiddle, by simp [DictionaryConstructor.insertRows, eval_bind, first],
          by simp [DictionaryConstructor.insertRows, eval_bind, otherFirst], retained, size, otherSize⟩
      | ok ignored =>
        obtain ⟨outcome, after, other, tail, otherTail, finalLayout, finalSize, otherFinalSize⟩ := ih retained
          (by simpa [size] using addressInside) (fun value member => by simpa [size] using rowsInside value (by simp [member]))
        exact ⟨outcome, after, other, by simpa [DictionaryConstructor.insertRows, eval_bind, first] using tail,
          by simpa [DictionaryConstructor.insertRows, eval_bind, otherFirst] using otherTail,
          finalLayout, finalSize.trans size, otherFinalSize.trans otherSize⟩


theorem dictionaryFromIterable_eq (heap : Heap) (source : Value) :
    DictionaryConstructor.fromIterable source heap = (do
      let rows ← DictionaryConstructor.iterable source
      DictionaryConstructor.insertRows heap.length rows
      pure (.ref heap.length) : Eval Value) (heap ++ [.dict []]) := by
  rfl

/-- Even acquisition errors follow the fresh allocation made by dict(iterable). -/
theorem ExecutionLayout.dictionaryFromIterable (layout : ExecutionLayout logical physical rename)
    (source : Value) (sourceInside : source.edge.Within logical.length) :
    let nextMap := extendMap rename logical.length physical.length
    ∃ outcome : Option (Except ExceptionObject Value), ∃ after other,
      DictionaryConstructor.fromIterable source logical = outcome.map (fun result => (result, after)) ∧
      DictionaryConstructor.fromIterable (relocateValue rename source) physical =
        outcome.map (fun result => (result.map (relocateValue nextMap), other)) ∧
      ExecutionLayout after other nextMap ∧ after.length = logical.length + 1 ∧ other.length = physical.length + 1 ∧
      (∀ value, outcome = some (.ok value) → value.edge.Within after.length) := by
  dsimp only
  let nextMap := extendMap rename logical.length physical.length
  let fresh := logical ++ [.dict []]
  let otherFresh := physical ++ [.dict []]
  have initial : ExecutionLayout fresh otherFresh nextMap := layout.append_existing (.dict []) (by simp) (by simp [ObjectWithin, objectValues])
  have sourceBound : source.edge.Within fresh.length := by
    cases source with
    | scalar scalar => trivial
    | ref address => simpa [Value.edge, Graph.Edge.Within, fresh] using Nat.lt_succ_of_lt sourceInside
  have sourceSame : relocateValue nextMap source = relocateValue rename source :=
    relocateValue_congr _ _ logical.length source (extendMap_old _ _ _) sourceInside
  have paired := initial.runtime.dictionaryIterable source sourceBound
  rw [sourceSame] at paired
  cases read : DictionaryConstructor.iterable source fresh with
  | none =>
    dsimp [fresh, otherFresh] at paired read
    refine ⟨none, fresh, otherFresh, ?_, ?_, initial, by simp [fresh], by simp [otherFresh], ?_⟩
    · simp [dictionaryFromIterable_eq, eval_bind, read]
    · simp [dictionaryFromIterable_eq, eval_bind, paired, read]
    · intro value impossible; cases impossible
  | some pair =>
    rcases pair with ⟨result, middle⟩
    have same := dictionaryIterable_heap fresh middle source sourceBound result read
    subst middle
    dsimp [fresh, otherFresh] at paired read
    cases result with
    | error exception =>
      refine ⟨some (.error exception), fresh, otherFresh, ?_, ?_, initial, by simp [fresh], by simp [otherFresh], ?_⟩
      · simp [dictionaryFromIterable_eq, eval_bind, read]; rfl
      · simp [dictionaryFromIterable_eq, eval_bind, paired, read, Except.map]; rfl
      · intro value impossible; cases impossible
    | ok rows =>
      obtain ⟨result, after, other, inserted, otherInserted, retained, size, otherSize⟩ :=
        initial.dictionaryInsertRows logical.length rows (by simp [fresh])
          (dictionaryIterable_bounded fresh initial.closed source sourceBound rows read)
      have freshAddress : nextMap logical.length = physical.length := extendMap_new _ _ _
      rw [freshAddress] at otherInserted
      dsimp [fresh, otherFresh] at inserted otherInserted
      refine ⟨result.map (Except.map (fun _ => .ref logical.length)), after, other, ?_, ?_, retained,
        by simpa [fresh] using size, by simpa [otherFresh] using otherSize, ?_⟩
      · cases result with
        | none => simp [dictionaryFromIterable_eq, eval_bind, read, inserted]
        | some outcome => cases outcome <;> simp [dictionaryFromIterable_eq, eval_bind, read, inserted, Except.map]
      · cases result with
        | none => simp [dictionaryFromIterable_eq, eval_bind, paired, read, otherInserted, Except.map]
        | some outcome => cases outcome <;>
            simp [dictionaryFromIterable_eq, eval_bind, paired, read, otherInserted, Except.map] <;> simp [relocateValue, extendMap_new]
      · intro value success
        cases result with
        | none => cases success
        | some outcome =>
          cases outcome with
          | error exception => cases success
          | ok ignored =>
            cases success
            simp [Value.edge, Graph.Edge.Within, size, fresh]

end FormalSW.PyAst.Mutable.Relocation
