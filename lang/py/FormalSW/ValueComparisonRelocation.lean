import lang.py.FormalSW.ComparisonRelocation
import lang.py.FormalSW.SetRelocation

/-! Value comparisons retain builtin dictionary, set, and instance semantics under relocation. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false
attribute [local simp] Except.bind Except.pure Except.map

theorem equalEntries_relocates (limit : Nat) (rename : Nat → Nat)
    (injective : Graph.Relocation.InjectiveBelow rename limit)
    (left right : List (Constant × Value))
    (leftInside : ∀ entry ∈ left, entry.2.edge.Within limit)
    (rightInside : ∀ entry ∈ right, entry.2.edge.Within limit) :
    HeapCalls.equalEntries (left.map fun entry => (entry.1, relocateValue rename entry.2))
        (right.map fun entry => (entry.1, relocateValue rename entry.2)) =
      HeapCalls.equalEntries left right := by
  induction left with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    have tail := ih (fun entry member => leftInside entry (by simp [member]))
    have head := leftInside (key, value) (by simp)
    simp only [List.map_cons, HeapCalls.equalEntries, scalarDict_lookup_relocates]
    cases found : ScalarDict.lookup right key with
    | none => rfl
    | some other =>
      have inside := ScalarDict.lookup_property right key (fun value => value.edge.Within limit) rightInside found
      have same := equalElements_relocates limit rename injective [value] [other]
        (by simpa using head) (by simpa using inside)
      simp only [List.map_cons, List.map_nil] at same
      simp only [Option.map_some, same, tail]

theorem equalDictionaries_relocates (limit : Nat) (rename : Nat → Nat)
    (injective : Graph.Relocation.InjectiveBelow rename limit)
    (left right : List (Constant × Value))
    (leftInside : ∀ entry ∈ left, entry.2.edge.Within limit)
    (rightInside : ∀ entry ∈ right, entry.2.edge.Within limit) :
    HeapCalls.equalDictionaries (left.map fun entry => (entry.1, relocateValue rename entry.2))
        (right.map fun entry => (entry.1, relocateValue rename entry.2)) =
      HeapCalls.equalDictionaries left right := by
  simp only [HeapCalls.equalDictionaries, List.length_map,
    equalEntries_relocates limit rename injective left right leftInside rightInside]

theorem dictionaryEntriesEqual_cons (entry : HashDict.Entry Value) (rest right : List (HashDict.Entry Value)) :
    HeapCalls.dictionaryEntriesEqual (entry :: rest) right = (do
      let some value := HashDict.lookup right entry.1 | some false
      let equal ← HeapCalls.equalLists [entry.2.2] [value]
      if equal then HeapCalls.dictionaryEntriesEqual rest right else some false) := rfl

theorem hash_lookup_within (entries : List (HashDict.Entry Value)) (limit : Nat) (key : HashKey) (value : Value)
    (inside : ∀ entry ∈ entries, entry.2.2.edge.Within limit)
    (found : HashDict.lookup entries key = some value) : value.edge.Within limit := by
  obtain ⟨entry, selected, same⟩ := Option.map_eq_some_iff.mp found
  rw [← same]
  exact inside entry (List.mem_of_find?_eq_some selected)

theorem dictionaryEntriesEqual_relocates (limit : Nat) (rename : Nat → Nat)
    (injective : Graph.Relocation.InjectiveBelow rename limit)
    (left right : List (HashDict.Entry Value))
    (leftInside : ∀ entry ∈ left, entry.2.2.edge.Within limit)
    (rightInside : ∀ entry ∈ right, entry.2.2.edge.Within limit) :
    HeapCalls.dictionaryEntriesEqual (relocateHashEntries rename left) (relocateHashEntries rename right) =
      HeapCalls.dictionaryEntriesEqual left right := by
  induction left with
  | nil => rfl
  | cons entry rest ih =>
    have tail := ih (fun entry member => leftInside entry (by simp [member]))
    simp only [relocateHashEntries] at tail
    have head := leftInside entry (by simp)
    simp only [relocateHashEntries, List.map_cons, dictionaryEntriesEqual_cons, hashDict_lookup_relocates]
    cases found : HashDict.lookup right entry.1 with
    | none => rfl
    | some other =>
      have inside := hash_lookup_within right limit entry.1 other rightInside found
      have same := equalLists_relocates limit rename injective [entry.2.2] [other]
        (by simpa using head) (by simpa using inside)
      simp only [List.map_cons, List.map_nil] at same
      simp only [Option.map_some, same, tail]

theorem keyDictionariesEqual_relocates (limit : Nat) (rename : Nat → Nat)
    (injective : Graph.Relocation.InjectiveBelow rename limit)
    (left right : List (HashDict.Entry Value))
    (leftInside : ∀ entry ∈ left, entry.2.2.edge.Within limit)
    (rightInside : ∀ entry ∈ right, entry.2.2.edge.Within limit) :
    HeapCalls.keyDictionariesEqual (relocateHashEntries rename left) (relocateHashEntries rename right) =
      HeapCalls.keyDictionariesEqual left right := by
  change (if (relocateHashEntries rename left).length = (relocateHashEntries rename right).length
    then HeapCalls.dictionaryEntriesEqual _ _ else some false) =
    (if left.length = right.length then HeapCalls.dictionaryEntriesEqual left right else some false)
  simp only [relocateHashEntries, List.length_map]
  have same := dictionaryEntriesEqual_relocates limit rename injective left right leftInside rightInside
  simp only [relocateHashEntries] at same
  rw [same]

theorem compareKeySets_relocates (rename : Nat → Nat) (op : CmpOp) (left right : List (HashKey × Value)) :
    Mutable.compareKeySets op (relocateKeyEntries rename left) (relocateKeyEntries rename right) =
      Mutable.compareKeySets op left right := by
  cases op <;> simp [Mutable.compareKeySets, relocateKeyEntries, Mutable.keyContains, List.all_map,
    List.any_map, Function.comp_def]

/-- Missing declared fields raise in declaration order, before value comparison. -/
def declaredValues (fields : List (String × Value)) : List String → Except ExceptionObject (List Value)
  | [] => .ok []
  | name :: rest => do
    let value ← match fields.lookup name with
      | some value => .ok value
      | none => .error { typeName := "AttributeError", args := [] }
    return value :: (← declaredValues fields rest)

theorem declaredValues_relocates (rename : Nat → Nat) (fields : List (String × Value)) (declared : List String) :
    declaredValues (fields.map fun field => (field.1, relocateValue rename field.2)) declared =
      (declaredValues fields declared).map (List.map (relocateValue rename)) := by
  induction declared with
  | nil => rfl
  | cons name rest ih =>
    simp only [declaredValues, fields_lookup_relocate]
    cases fields.lookup name with
    | none => rfl
    | some value =>
      simp only [Option.map_some, ih]
      cases declaredValues fields rest <;> rfl

theorem declaredValues_within (fields : List (String × Value)) (declared : List String) (limit : Nat)
    (inside : ∀ field ∈ fields, field.2.edge.Within limit) (values : List Value)
    (selected : declaredValues fields declared = .ok values) :
    ∀ value ∈ values, value.edge.Within limit := by
  induction declared generalizing values with
  | nil => cases selected; simp
  | cons name rest ih =>
    cases found : fields.lookup name with
    | none => simp [declaredValues, found, bind] at selected
    | some value =>
      have head : value.edge.Within limit := by
        obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp found
        exact inside (name, value) (by simp [same])
      cases remaining : declaredValues fields rest with
      | error exception => simp [declaredValues, found, remaining, bind] at selected
      | ok tail =>
        have same : value :: tail = values := by simpa [declaredValues, found, remaining, bind, pure] using selected
        subst values
        simpa using And.intro head (ih tail remaining)

theorem declaredValues_eval (heap : Heap) (fields : List (String × Value)) (declared : List String) :
    (declared.mapM (fun name => match fields.lookup name with
      | some value => (pure value : Eval Value)
      | none => throw ({ typeName := "AttributeError", args := [] } : ExceptionObject))) heap =
      some (declaredValues fields declared, heap) := by
  induction declared with
  | nil => rfl
  | cons name rest ih =>
    simp only [List.mapM_cons, eval_bind, declaredValues]
    cases found : fields.lookup name with
    | none => rfl
    | some value => simp [ih]; cases declaredValues fields rest <;> rfl

/-- Read-only comparison results contain booleans or an exception, never an allocated reference. -/
def comparisonEval (result : HeapSort.Result Bool) : Eval Value := fun heap =>
  result.map fun outcome => (outcome.map (fun answer => Value.scalar (.bool answer)), heap)

theorem comparisonEval_relocates (result : HeapSort.Result Bool) (logical physical : Heap) (rename : Nat → Nat) :
    comparisonEval result physical = (comparisonEval result logical).map
      (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  cases result with
  | none => rfl
  | some outcome => cases outcome <;> rfl

def equalityAnswer (op : CmpOp) (answer : Option Bool) : HeapSort.Result Bool :=
  match op with
  | .eq => answer.map Except.ok
  | .notEq => answer.map (fun equal => Except.ok (!equal))
  | _ => HeapSort.typeError

theorem compare_dicts_eq (heap : Heap) (op : CmpOp) (a b : Nat) (xs ys : List (Constant × Value))
    (first : heap[a]? = some (.dict xs)) (second : heap[b]? = some (.dict ys)) :
    HeapCalls.compare op (.ref a) (.ref b) heap =
      comparisonEval (equalityAnswer op (if a = b then some true else HeapCalls.equalDictionaries xs ys)) heap := by
  cases equal : (if a = b then some true else HeapCalls.equalDictionaries xs ys) <;> cases op <;>
    simp [HeapCalls.compare, first, second, comparisonEval, equalityAnswer, equal,
      HeapSort.typeError, error, unsupported] <;> rfl

theorem compare_dict_keyDict_eq (heap : Heap) (op : CmpOp) (a b : Nat)
    (xs : List (Constant × Value)) (ys : List (HashDict.Entry Value))
    (first : heap[a]? = some (.dict xs)) (second : heap[b]? = some (.keyDict ys)) :
    HeapCalls.compare op (.ref a) (.ref b) heap =
      comparisonEval (equalityAnswer op (HeapCalls.keyDictionariesEqual (Mutable.promoteDictionary xs) ys)) heap := by
  cases equal : HeapCalls.keyDictionariesEqual (Mutable.promoteDictionary xs) ys <;> cases op <;>
    simp only [HeapCalls.keyDictionariesEqual] at equal ⊢ <;>
    simp [HeapCalls.compare, first, second, comparisonEval, equalityAnswer, equal,
      HeapSort.typeError, error, unsupported] <;> rfl

theorem compare_keyDict_eq (heap : Heap) (op : CmpOp) (a b : Nat)
    (xs ys : List (HashDict.Entry Value)) (object : Object)
    (first : heap[a]? = some (.keyDict xs)) (second : heap[b]? = some object)
    (entries : Mutable.dictionaryEntries object = some ys) :
    HeapCalls.compare op (.ref a) (.ref b) heap =
      comparisonEval (equalityAnswer op (if a = b then some true else HeapCalls.keyDictionariesEqual xs ys)) heap := by
  cases equal : (if a = b then some true else HeapCalls.keyDictionariesEqual xs ys) <;> cases op <;>
    simp only [HeapCalls.keyDictionariesEqual] at equal ⊢ <;>
    simp [HeapCalls.compare, first, second, entries, comparisonEval, equalityAnswer, equal,
      HeapSort.typeError, error, unsupported] <;> rfl

theorem dictionaryEntries_relocates (rename : Nat → Nat) (object : Object) :
    Mutable.dictionaryEntries (relocateObject rename object) =
      (Mutable.dictionaryEntries object).map (relocateHashEntries rename) := by
  cases object <;> simp [Mutable.dictionaryEntries, relocateObject, promoteDictionary_relocates, relocateHashEntries]

theorem dictionaryEntries_within (object : Object) (limit : Nat) (entries : List (HashDict.Entry Value))
    (inside : ObjectWithin limit object) (found : Mutable.dictionaryEntries object = some entries) :
    ∀ entry ∈ entries, entry.2.2.edge.Within limit := by
  cases object <;> simp only [Mutable.dictionaryEntries, Option.some.injEq] at found
  all_goals first
    | contradiction
    | subst entries
      intro entry member
      obtain ⟨pair, present, rfl⟩ := List.mem_map.mp member
      exact inside pair.2 (List.mem_map.mpr ⟨pair, present, rfl⟩)
    | subst entries
      intro entry member
      exact inside entry.2.2 (List.mem_flatMap.mpr ⟨entry, member, by simp⟩)

theorem RuntimeLayout.compare_dicts {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (op : CmpOp) (a b : Nat) (xs ys : List (Constant × Value))
    (first : logical[a]? = some (.dict xs)) (second : logical[b]? = some (.dict ys)) :
    HeapCalls.compare op (.ref (rename a)) (.ref (rename b)) physical =
      (HeapCalls.compare op (.ref a) (.ref b) logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  have same : rename a = rename b ↔ a = b :=
    ⟨layout.injective a (List.getElem?_eq_some_iff.mp first).1 b (List.getElem?_eq_some_iff.mp second).1,
      congrArg rename⟩
  have leftInside : ∀ entry ∈ xs, entry.2.edge.Within logical.length :=
    fun entry member => closed _ (List.mem_of_getElem? first) entry.2 (List.mem_map.mpr ⟨entry, member, rfl⟩)
  have rightInside : ∀ entry ∈ ys, entry.2.edge.Within logical.length :=
    fun entry member => closed _ (List.mem_of_getElem? second) entry.2 (List.mem_map.mpr ⟨entry, member, rfl⟩)
  rw [compare_dicts_eq logical op a b xs ys first second,
    compare_dicts_eq physical op (rename a) (rename b) _ _ (layout.lookup a _ first) (layout.lookup b _ second)]
  simp only [same, equalDictionaries_relocates logical.length rename layout.injective xs ys leftInside rightInside]
  exact comparisonEval_relocates _ logical physical rename

theorem RuntimeLayout.compare_dict_keyDict {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (op : CmpOp) (a b : Nat) (xs : List (Constant × Value)) (ys : List (HashDict.Entry Value))
    (first : logical[a]? = some (.dict xs)) (second : logical[b]? = some (.keyDict ys)) :
    HeapCalls.compare op (.ref (rename a)) (.ref (rename b)) physical =
      (HeapCalls.compare op (.ref a) (.ref b) logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  have leftInside := dictionaryEntries_within (.dict xs) logical.length _
    (closed _ (List.mem_of_getElem? first)) rfl
  have rightInside := dictionaryEntries_within (.keyDict ys) logical.length ys
    (closed _ (List.mem_of_getElem? second)) rfl
  rw [compare_dict_keyDict_eq logical op a b xs ys first second,
    compare_dict_keyDict_eq physical op (rename a) (rename b) _ _ (layout.lookup a _ first) (layout.lookup b _ second)]
  rw [promoteDictionary_relocates]
  change comparisonEval (equalityAnswer op (HeapCalls.keyDictionariesEqual
    (relocateHashEntries rename (Mutable.promoteDictionary xs)) (relocateHashEntries rename ys))) physical = _
  rw [keyDictionariesEqual_relocates logical.length rename layout.injective _ _ leftInside rightInside]
  exact comparisonEval_relocates _ logical physical rename

theorem RuntimeLayout.compare_keyDict {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (op : CmpOp) (a b : Nat) (xs ys : List (HashDict.Entry Value)) (object : Object)
    (first : logical[a]? = some (.keyDict xs)) (second : logical[b]? = some object)
    (entries : Mutable.dictionaryEntries object = some ys) :
    HeapCalls.compare op (.ref (rename a)) (.ref (rename b)) physical =
      (HeapCalls.compare op (.ref a) (.ref b) logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  have leftInside := dictionaryEntries_within (.keyDict xs) logical.length xs
    (closed _ (List.mem_of_getElem? first)) rfl
  have rightInside := dictionaryEntries_within object logical.length ys
    (closed _ (List.mem_of_getElem? second)) entries
  have same : rename a = rename b ↔ a = b :=
    ⟨layout.injective a (List.getElem?_eq_some_iff.mp first).1 b (List.getElem?_eq_some_iff.mp second).1,
      congrArg rename⟩
  have movedEntries : Mutable.dictionaryEntries (relocateObject rename object) = some (relocateHashEntries rename ys) := by
    rw [dictionaryEntries_relocates, entries]; rfl
  rw [compare_keyDict_eq logical op a b xs ys object first second entries,
    compare_keyDict_eq physical op (rename a) (rename b) _ _ _ (layout.lookup a _ first)
      (layout.lookup b _ second) movedEntries]
  change comparisonEval (equalityAnswer op (if rename a = rename b then some true else
    HeapCalls.keyDictionariesEqual (relocateHashEntries rename xs) (relocateHashEntries rename ys))) physical = _
  simp only [same, keyDictionariesEqual_relocates logical.length rename layout.injective xs ys leftInside rightInside]
  exact comparisonEval_relocates _ logical physical rename

def dataEqualityAnswer (op : CmpOp) (declared : List String) (left right : List (String × Value)) :
    HeapSort.Result Bool :=
  match op with
  | .eq | .notEq =>
    match declaredValues left declared with
    | .error exception => some (.error exception)
    | .ok xs => match declaredValues right declared with
      | .error exception => some (.error exception)
      | .ok ys => equalityAnswer op (HeapCalls.equalLists xs ys)
  | _ => HeapSort.typeError

theorem dataEqualityAnswer_relocates (limit : Nat) (rename : Nat → Nat)
    (injective : Graph.Relocation.InjectiveBelow rename limit) (op : CmpOp) (declared : List String)
    (left right : List (String × Value))
    (leftInside : ∀ field ∈ left, field.2.edge.Within limit)
    (rightInside : ∀ field ∈ right, field.2.edge.Within limit) :
    dataEqualityAnswer op declared (left.map fun field => (field.1, relocateValue rename field.2))
      (right.map fun field => (field.1, relocateValue rename field.2)) =
      dataEqualityAnswer op declared left right := by
  cases op <;> simp only [dataEqualityAnswer, declaredValues_relocates]
  all_goals
    cases first : declaredValues left declared with
    | error exception => rfl
    | ok xs =>
      cases second : declaredValues right declared with
      | error exception => rfl
      | ok ys =>
        have same := equalLists_relocates limit rename injective xs ys
          (declaredValues_within left declared limit leftInside xs first)
          (declaredValues_within right declared limit rightInside ys second)
        simp only [Except.map, same]

theorem compare_dataInstances_eq (heap : Heap) (op : CmpOp) (a b : Nat)
    (origin name : String) (frozen : Bool) (declared : List String) (fields : List (String × Value))
    (otherOrigin otherName : String) (otherFrozen : Bool) (otherDeclared : List String)
    (otherFields : List (String × Value))
    (first : heap[a]? = some (.dataInstance origin name frozen declared fields))
    (second : heap[b]? = some (.dataInstance otherOrigin otherName otherFrozen otherDeclared otherFields)) :
    HeapCalls.compare op (.ref a) (.ref b) heap =
      if origin ≠ otherOrigin ∨ name ≠ otherName then HeapCalls.compareDifferent op heap
      else if frozen ≠ otherFrozen ∨ declared ≠ otherDeclared then none
      else comparisonEval (if a = b then equalityAnswer op (some true)
        else dataEqualityAnswer op declared fields otherFields) heap := by
  by_cases different : origin ≠ otherOrigin ∨ name ≠ otherName
  · simp [HeapCalls.compare, first, second, different]
  · by_cases mismatch : frozen ≠ otherFrozen ∨ declared ≠ otherDeclared
    · simp [HeapCalls.compare, first, second, different, mismatch, unsupported]
    · by_cases same : a = b
      · cases op <;>
          simp [HeapCalls.compare, second, different, mismatch, same,
            equalityAnswer, comparisonEval, HeapSort.typeError, error, Except.map] <;> rfl
      · cases op <;>
          simp [HeapCalls.compare, first, second, different, mismatch, same, dataEqualityAnswer,
            comparisonEval, HeapSort.typeError, error, eval_bind]
        all_goals erw [declaredValues_eval heap fields declared]
        all_goals
          cases leftValues : declaredValues fields declared with
          | error exception => simp
          | ok xs =>
            simp only [Option.bind_some]
            erw [declaredValues_eval heap otherFields declared]
            cases rightValues : declaredValues otherFields declared with
            | error exception => simp
            | ok ys =>
              cases equal : HeapCalls.equalLists xs ys <;>
                simp [equal, equalityAnswer, unsupported] <;> rfl

/-- Python 3.14's generated equality checks identity before reading declared fields. -/
theorem compare_dataInstance_self (heap : Heap) (address : Nat) (origin name : String) (frozen : Bool)
    (declared : List String) (fields : List (String × Value)) (negated : Bool)
    (found : heap[address]? = some (.dataInstance origin name frozen declared fields)) :
    HeapCalls.compare (if negated then .notEq else .eq) (.ref address) (.ref address) heap =
      some (.ok (.scalar (.bool (!negated))), heap) := by
  rw [compare_dataInstances_eq heap _ address address origin name frozen declared fields
    origin name frozen declared fields found found]
  cases negated <;> simp [equalityAnswer, comparisonEval, Except.map]

theorem RuntimeLayout.compare_dataInstances {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical) (op : CmpOp) (a b : Nat)
    (origin name : String) (frozen : Bool) (declared : List String) (fields : List (String × Value))
    (otherOrigin otherName : String) (otherFrozen : Bool) (otherDeclared : List String)
    (otherFields : List (String × Value))
    (first : logical[a]? = some (.dataInstance origin name frozen declared fields))
    (second : logical[b]? = some (.dataInstance otherOrigin otherName otherFrozen otherDeclared otherFields)) :
    HeapCalls.compare op (.ref (rename a)) (.ref (rename b)) physical =
      (HeapCalls.compare op (.ref a) (.ref b) logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  have movedFirst := layout.lookup a _ first
  have movedSecond := layout.lookup b _ second
  simp only [relocateObject] at movedFirst movedSecond
  rw [compare_dataInstances_eq logical op a b _ _ _ _ _ _ _ _ _ _ first second,
    compare_dataInstances_eq physical op (rename a) (rename b) _ _ _ _ _ _ _ _ _ _ movedFirst movedSecond]
  have same : rename a = rename b ↔ a = b :=
    ⟨layout.injective a (List.getElem?_eq_some_iff.mp first).1 b (List.getElem?_eq_some_iff.mp second).1,
      congrArg rename⟩
  simp only [same]
  have leftInside : ∀ field ∈ fields, field.2.edge.Within logical.length := by
    intro field member
    exact closed _ (List.mem_of_getElem? first) field.2 (List.mem_map.mpr ⟨field, member, rfl⟩)
  have rightInside : ∀ field ∈ otherFields, field.2.edge.Within logical.length := by
    intro field member
    exact closed _ (List.mem_of_getElem? second) field.2 (List.mem_map.mpr ⟨field, member, rfl⟩)
  rw [dataEqualityAnswer_relocates logical.length rename layout.injective op declared fields otherFields
    leftInside rightInside]
  split
  · cases op <;> rfl
  · split
    · rfl
    · exact comparisonEval_relocates _ logical physical rename

end FormalSW.PyAst.Mutable.Relocation
