import lang.py.FormalSW.MutableRelocation
import lang.py.FormalSW.Instances

/-! Runtime object relocation retains metadata erased by observable snapshots. -/
namespace FormalSW.PyAst.Mutable.Relocation
open Graph.Relocation
set_option Elab.async false

/-- Cached immutable keys contain values, not heap addresses. -/
def relocateObject (rename : Nat → Nat) : Object → Object
  | .list items => .list (items.map (relocateValue rename))
  | .tuple items => .tuple (items.map (relocateValue rename))
  | .bytearray bytes => .bytearray bytes
  | .set items => .set items
  | .keySet items => .keySet (items.map fun entry => (entry.1, relocateValue rename entry.2))
  | .dict entries => .dict (entries.map fun entry => (entry.1, relocateValue rename entry.2))
  | .keyDict entries => .keyDict (entries.map fun entry =>
      (entry.1, relocateValue rename entry.2.1, relocateValue rename entry.2.2))
  | .instance origin name fields =>
      .instance origin name (fields.map fun field => (field.1, relocateValue rename field.2))
  | .dataInstance origin name frozen declared fields =>
      .dataInstance origin name frozen declared
        (fields.map fun field => (field.1, relocateValue rename field.2))

/-- Every stored value, including representatives of hashed keys. -/
def objectValues : Object → List Value
  | .list items | .tuple items => items
  | .bytearray _ | .set _ => []
  | .keySet items => items.map Prod.snd
  | .dict entries => entries.map Prod.snd
  | .keyDict entries => entries.flatMap fun entry => [entry.2.1, entry.2.2]
  | .instance _ _ fields | .dataInstance _ _ _ _ fields => fields.map Prod.snd

def ObjectWithin (limit : Nat) (object : Object) : Prop :=
  ∀ value ∈ objectValues object, value.edge.Within limit

def Closed (heap : Heap) : Prop := ∀ object ∈ heap, ObjectWithin heap.length object

/-- Exact runtime objects correspond, including flags, declared fields, and cached keys.
Unrepresented physical objects may be interleaved with this logical heap. -/
structure RuntimeLayout (logical physical : Heap) (rename : Nat → Nat) : Prop where
  injective : InjectiveBelow rename logical.length
  lookup : ∀ index object, logical[index]? = some object →
    physical[rename index]? = some (relocateObject rename object)

variable {logical physical : Heap} {rename : Nat → Nat}

@[simp] theorem relocateValue_id (value : Value) : relocateValue id value = value := by
  cases value <;> rfl

@[simp] theorem relocateObject_id (object : Object) : relocateObject id object = object := by
  have same : relocateValue id = id := funext relocateValue_id
  cases object <;> simp [relocateObject, same]

@[simp] theorem relocateValue_comp (first second : Nat → Nat) (value : Value) :
    relocateValue second (relocateValue first value) = relocateValue (second ∘ first) value := by
  cases value <;> rfl

@[simp] theorem relocateObject_comp (first second : Nat → Nat) (object : Object) :
    relocateObject second (relocateObject first object) = relocateObject (second ∘ first) object := by
  cases object <;> simp [relocateObject, List.map_map, Function.comp_def]

theorem RuntimeLayout.refl (heap : Heap) : RuntimeLayout heap heap id := by
  refine ⟨?_, ?_⟩
  · intro i _ j _ same
    exact same
  · intro index object found
    simpa using found

theorem RuntimeLayout.bound (layout : RuntimeLayout logical physical rename)
    (index : Nat) (inside : index < logical.length) : rename index < physical.length := by
  have found := layout.lookup index logical[index] (List.getElem?_eq_getElem inside)
  exact (List.getElem?_eq_some_iff.mp found).1

theorem RuntimeLayout.trans {middle last : Heap} {firstMap secondMap : Nat → Nat}
    (first : RuntimeLayout logical middle firstMap)
    (second : RuntimeLayout middle last secondMap) :
    RuntimeLayout logical last (secondMap ∘ firstMap) := by
  constructor
  · intro i hi j hj equal
    exact first.injective i hi j hj
      (second.injective _ (first.bound i hi) _ (first.bound j hj) equal)
  · intro index object found
    simpa using second.lookup (firstMap index) _ (first.lookup index object found)

theorem RuntimeLayout.preserves {after : Heap} (layout : RuntimeLayout logical physical rename)
    (retained : ∀ index < logical.length, after[rename index]? = physical[rename index]?) :
    RuntimeLayout logical after rename := by
  refine ⟨layout.injective, ?_⟩
  intro index object found
  rw [retained index (List.getElem?_eq_some_iff.mp found).1]
  exact layout.lookup index object found

theorem RuntimeLayout.append_private (layout : RuntimeLayout logical physical rename) (extra : Heap) :
    RuntimeLayout logical (physical ++ extra) rename :=
  layout.preserves (fun index inside => List.getElem?_append_left (layout.bound index inside))

theorem relocateValue_congr (left right : Nat → Nat) (limit : Nat) (value : Value)
    (agree : ∀ index < limit, left index = right index) (inside : value.edge.Within limit) :
    relocateValue left value = relocateValue right value := by
  cases value with
  | scalar value => rfl
  | ref index => exact congrArg Value.ref (agree index inside)

theorem relocateObject_congr (left right : Nat → Nat) (limit : Nat) (object : Object)
    (agree : ∀ index < limit, left index = right index) (inside : ObjectWithin limit object) :
    relocateObject left object = relocateObject right object := by
  have values : ∀ value ∈ objectValues object,
      relocateValue left value = relocateValue right value := by
    intro value member
    exact relocateValue_congr left right limit value agree (inside value member)
  cases object with
  | bytearray bytes | set items => rfl
  | list items | tuple items =>
    simp only [relocateObject]
    congr 1
    exact List.map_congr_left values
  | keySet items | dict items | «instance» origin name items | dataInstance origin name frozen declared items =>
    simp only [relocateObject]
    congr 1
    apply List.map_congr_left
    intro entry member
    exact congrArg (fun value => (entry.1, value))
      (values entry.2 (List.mem_map.mpr ⟨entry, member, rfl⟩))
  | keyDict items =>
    simp only [relocateObject]
    congr 1
    apply List.map_congr_left
    intro entry member
    have first := values entry.2.1 (List.mem_flatMap.mpr ⟨entry, member, by simp⟩)
    have second := values entry.2.2 (List.mem_flatMap.mpr ⟨entry, member, by simp⟩)
    simp [first, second]

/-- Updating a corresponding cell cannot overwrite a distinct logical object. -/
theorem RuntimeLayout.set (layout : RuntimeLayout logical physical rename)
    (index : Nat) (inside : index < logical.length) (object : Object) :
    RuntimeLayout (logical.set index object)
      (physical.set (rename index) (relocateObject rename object)) rename := by
  constructor
  · simpa only [List.length_set] using layout.injective
  · intro observed current found
    have bound : observed < logical.length := by
      simpa only [List.length_set] using (List.getElem?_eq_some_iff.mp found).1
    by_cases same : observed = index
    · subst observed
      have equal : current = object := by simpa [List.getElem?_set, inside] using found.symm
      subst current
      simp [layout.bound index inside]
    · have different : rename index ≠ rename observed := by
        intro equal
        exact same (layout.injective observed bound index inside equal.symm)
      have old : logical[observed]? = some current := by
        simpa [List.getElem?_set, same, Ne.symm same] using found
      simpa [different] using layout.lookup observed current old

/-- Extend the address map only at the newly allocated logical address. -/
def extendMap (rename : Nat → Nat) (logicalSize physicalAddress index : Nat) : Nat :=
  if index = logicalSize then physicalAddress else rename index

@[simp] theorem extendMap_old (rename : Nat → Nat) (logicalSize physicalAddress index : Nat)
    (inside : index < logicalSize) :
    extendMap rename logicalSize physicalAddress index = rename index := by
  simp [extendMap, Nat.ne_of_lt inside]

@[simp] theorem extendMap_new (rename : Nat → Nat) (logicalSize physicalAddress : Nat) :
    extendMap rename logicalSize physicalAddress logicalSize = physicalAddress := by
  simp [extendMap]

/-- Fresh corresponding allocations extend the relation without requiring equal heap lengths. -/
theorem RuntimeLayout.allocate (layout : RuntimeLayout logical physical rename)
    (closed : Closed logical) (object : Object) :
    let nextMap := extendMap rename logical.length physical.length
    RuntimeLayout (logical ++ [object]) (physical ++ [relocateObject nextMap object]) nextMap := by
  dsimp only
  constructor
  · intro i hi j hj equal
    simp only [List.length_append, List.length_singleton] at hi hj
    by_cases freshI : i = logical.length <;> by_cases freshJ : j = logical.length
    · omega
    · have oldJ : j < logical.length := by omega
      have below := layout.bound j oldJ
      simp only [freshI, extendMap_new, extendMap_old _ _ _ _ oldJ] at equal
      omega
    · have oldI : i < logical.length := by omega
      have below := layout.bound i oldI
      simp only [freshJ, extendMap_new, extendMap_old _ _ _ _ oldI] at equal
      omega
    · have oldI : i < logical.length := by omega
      have oldJ : j < logical.length := by omega
      simp only [extendMap_old _ _ _ _ oldI, extendMap_old _ _ _ _ oldJ] at equal
      exact layout.injective i oldI j oldJ equal
  · intro index current found
    by_cases old : index < logical.length
    · have original : logical[index]? = some current := by
        simpa [List.getElem?_append, old] using found
      rw [extendMap_old _ _ _ _ old, List.getElem?_append_left (layout.bound index old)]
      rw [layout.lookup index current original]
      congr 1
      exact relocateObject_congr _ _ logical.length current
        (fun i hi => (extendMap_old _ _ _ _ hi).symm)
        (closed current (List.mem_of_getElem? original))
    · have indexBound := (List.getElem?_eq_some_iff.mp found).1
      have equal : index = logical.length := by
        simp only [List.length_append, List.length_singleton] at indexBound
        omega
      subst index
      have same : current = object := by simpa using found.symm
      subst current
      simp


/-- Valid modeled heaps are closed even when immutable tuple references are shared. -/
theorem closed_of_valid (heap : Heap) (valid : heap.Valid) : Closed heap := by
  intro object member value valueMember
  have supported := valid object member
  cases object with
  | list items | tuple items =>
    have inside := supported value valueMember
    cases value <;> exact inside
  | bytearray bytes | set items => simp [objectValues] at valueMember
  | dict entries | «instance» origin name entries | dataInstance origin name frozen declared entries =>
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp valueMember
    have inside := supported.2 entry present
    cases value : entry.2 with
    | scalar _ => trivial
    | ref _ => simpa only [value] using inside
  | keySet entries =>
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp valueMember
    have inside := (supported.2 entry present).2
    cases value : entry.2 with
    | scalar _ => trivial
    | ref _ => simpa only [value] using inside
  | keyDict entries =>
    obtain ⟨entry, present, position⟩ := List.mem_flatMap.mp valueMember
    rcases List.mem_cons.mp position with rfl | last
    · exact (supported.2 entry present).2.1
    · exact List.mem_singleton.mp last ▸ (supported.2 entry present).2.2

private theorem canonicalKeys_relocate (rename : Nat → Nat) (items : List (HashKey × Value)) :
    canonicalKeys (items.map fun entry => (entry.1, relocateValue rename entry.2)) =
      (canonicalKeys items).map (fun entry => (entry.1, relocateValue rename entry.2)) := by
  exact (List.map_mergeSort
    (f := fun entry : HashKey × Value => (entry.1, relocateValue rename entry.2))
    (r := fun a b => HashKey.before a.1 b.1) (s := fun a b => HashKey.before a.1 b.1)
    (l := items) (fun _ _ _ _ => rfl)).symm

/-- Exact runtime relocation implies the weaker snapshot relation. -/
theorem graphNode_relocate (rename : Nat → Nat) (object : Object) :
    graphNode (relocateObject rename object) = relocateNode rename (graphNode object) := by
  cases object <;>
    simp [relocateObject, graphNode, relocateNode, relocateEdge, canonicalKeys_relocate,
      List.map_map, List.map_flatMap, List.flatMap_map, Function.comp_def]

theorem RuntimeLayout.snapshot (layout : RuntimeLayout logical physical rename) :
    HeapLayout logical physical rename := by
  refine ⟨?_, ?_⟩
  · simpa only [List.length_map] using layout.injective
  · intro index node found
    obtain ⟨object, original, equal⟩ := Option.map_eq_some_iff.mp
      (show (logical[index]?).map graphNode = some node from by simpa using found)
    subst node
    simp [layout.lookup index object original, graphNode_relocate]

/-- List allocation extends the runtime relation using the actual allocator on both sides. -/
theorem RuntimeLayout.allocate_list (layout : RuntimeLayout logical physical rename)
    (closed : Closed logical) (items : List Value)
    (inside : ∀ value ∈ items, value.edge.Within logical.length) :
    let nextMap := extendMap rename logical.length physical.length
    Mutable.allocate items logical = some (.ok (.ref logical.length), logical ++ [.list items]) ∧
    Mutable.allocate (items.map (relocateValue rename)) physical =
      some (.ok (.ref physical.length), physical ++ [.list (items.map (relocateValue rename))]) ∧
    RuntimeLayout (logical ++ [.list items])
      (physical ++ [.list (items.map (relocateValue rename))]) nextMap := by
  dsimp only
  refine ⟨rfl, rfl, ?_⟩
  have same : relocateObject (extendMap rename logical.length physical.length) (.list items) =
      relocateObject rename (.list items) :=
    relocateObject_congr _ _ logical.length (.list items)
      (fun index bound => extendMap_old _ _ _ _ bound) inside
  have allocated := layout.allocate closed (.list items)
  dsimp only at allocated
  rw [same] at allocated
  exact allocated

/-- Field order and names are retained under value relocation. -/
theorem fields_lookup_relocate (rename : Nat → Nat) (fields : List (String × Value)) (name : String) :
    (fields.map fun field => (field.1, relocateValue rename field.2)).lookup name =
      (fields.lookup name).map (relocateValue rename) := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    rcases field with ⟨key, value⟩
    by_cases same : name = key
    · simp [List.lookup, same]
    · simp [List.lookup, ih, beq_eq_false_iff_ne.mpr same]

theorem putField_relocate (rename : Nat → Nat) (fields : List (String × Value))
    (name : String) (value : Value) :
    putField (fields.map fun field => (field.1, relocateValue rename field.2)) name
      (relocateValue rename value) =
      (putField fields name value).map (fun field => (field.1, relocateValue rename field.2)) := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    rcases field with ⟨key, old⟩
    by_cases same : key = name <;> simp [putField, same, ih]

/-- Reading a relocated field preserves its value, absence, and unsupported-attribute behavior. -/
theorem RuntimeLayout.readField (layout : RuntimeLayout logical physical rename)
    (receiver : Value) (name : String) (inside : receiver.edge.Within logical.length) :
    readField (relocateValue rename receiver) name physical =
      (readField receiver name logical).map
        (fun result => (result.1.map (relocateValue rename), physical)) := by
  by_cases special : name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__"
  · simp [Mutable.readField, special, unsupported]
  · cases receiver with
    | scalar value => simp [Mutable.readField, instanceData, relocateValue, special, error, Except.map]
    | ref index =>
      have found : logical[index]? = some logical[index] := List.getElem?_eq_getElem inside
      have moved := layout.lookup index _ found
      cases object : logical[index] with
      | «instance» origin className fields | dataInstance origin className frozen declared fields =>
        simp only [object, relocateObject] at moved
        change Mutable.readField (.ref (rename index)) name physical = _
        cases field : fields.lookup name <;>
          simp [Mutable.readField, instanceData, special, found, object,
            moved, error, fields_lookup_relocate, field, Except.map]
      | list items | tuple items | bytearray bytes | set items | keySet items | dict entries | keyDict entries =>
        simp only [object, relocateObject] at moved
        change Mutable.readField (.ref (rename index)) name physical = _
        simp [Mutable.readField, instanceData, special, found, object, moved, error, Except.map]

/-- Field writes and their errors agree under relocation, retaining the full runtime layout. -/
theorem RuntimeLayout.writeField (layout : RuntimeLayout logical physical rename)
    (receiver : Value) (name : String) (value : Value)
    (inside : receiver.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.writeField receiver name value logical = some (outcome, after)) :
    ∃ other, Mutable.writeField (relocateValue rename receiver) name (relocateValue rename value)
      physical = some (outcome.map (relocateValue rename), other) ∧
      RuntimeLayout after other rename := by
  have unchanged (error : ExceptionObject)
      (leftRun : Mutable.writeField receiver name value logical = some (.error error, logical))
      (rightRun : Mutable.writeField (relocateValue rename receiver) name
        (relocateValue rename value) physical = some (.error error, physical)) :
      ∃ other, Mutable.writeField (relocateValue rename receiver) name (relocateValue rename value)
        physical = some (outcome.map (relocateValue rename), other) ∧
        RuntimeLayout after other rename := by
    rw [leftRun] at executed
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
    exact ⟨physical, rightRun, layout⟩
  by_cases special : name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__"
  · simp [Mutable.writeField, special, unsupported] at executed
  · cases receiver with
    | scalar scalar =>
      apply unchanged ⟨"AttributeError", []⟩ <;>
        simp [Mutable.writeField, instanceData, relocateValue, special, error]
    | ref index =>
      have found : logical[index]? = some logical[index] := List.getElem?_eq_getElem inside
      have moved := layout.lookup index _ found
      cases object : logical[index] with
      | «instance» origin className fields =>
        simp only [object, relocateObject] at moved
        have original : Mutable.writeField (.ref index) name value logical =
            some (.ok (.scalar .none), logical.set index
              (.instance origin className (putField fields name value))) := by
          simp [Mutable.writeField, instanceData, special, found, object, Except.map]
        rw [original] at executed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
        refine ⟨physical.set (rename index) (relocateObject rename
          (.instance origin className (putField fields name value))), ?_, layout.set index inside _⟩
        change Mutable.writeField (.ref (rename index)) name (relocateValue rename value) physical =
          some (.ok (.scalar .none), _)
        simp [Mutable.writeField, instanceData, special, moved, relocateObject,
          putField_relocate, Except.map]
      | dataInstance origin className frozen declared fields =>
        simp only [object, relocateObject] at moved
        cases frozen with
        | true =>
          apply unchanged ⟨"FrozenInstanceError", []⟩ <;>
            simp [Mutable.writeField, instanceData, relocateValue, special, found, object, moved, error]
        | false =>
          have original : Mutable.writeField (.ref index) name value logical =
              some (.ok (.scalar .none), logical.set index
                (.dataInstance origin className false declared (putField fields name value))) := by
            simp [Mutable.writeField, instanceData, special, found, object, Except.map]
          rw [original] at executed
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
          refine ⟨physical.set (rename index) (relocateObject rename
            (.dataInstance origin className false declared (putField fields name value))), ?_,
            layout.set index inside _⟩
          change Mutable.writeField (.ref (rename index)) name (relocateValue rename value) physical =
            some (.ok (.scalar .none), _)
          simp [Mutable.writeField, instanceData, special, moved, relocateObject,
            putField_relocate, Except.map]
      | list items | tuple items | bytearray bytes | set items | keySet items | dict entries | keyDict entries =>
        simp only [object, relocateObject] at moved
        apply unchanged ⟨"AttributeError", []⟩ <;>
          simp [Mutable.writeField, instanceData, relocateValue, special, found, object, moved, error]

end FormalSW.PyAst.Mutable.Relocation
