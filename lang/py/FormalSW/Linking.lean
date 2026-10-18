import lang.py.FormalSW.Calls

namespace FormalSW.PyAst.Calls

/-- A linked program preserves every function and modeled library call of a
source module. New names may be added, but existing meanings cannot change. -/
structure Extends (target source : Module) : Prop where
  functions : ∀ name args body,
    findFunctionIn source.body name = some (args, body) →
    findFunctionIn target.body name = some (args, body)
  libraries : ∀ name values result,
    findFunctionIn source.body name = none →
    libraryCall source name values = some result →
    findFunctionIn target.body name = none ∧ libraryCall target name values = some result

theorem Extends.refl (module : Module) : Extends module module :=
  ⟨fun _ _ _ h => h, fun _ _ _ absent result => ⟨absent, result⟩⟩

theorem Extends.trans (first : Extends middle source) (second : Extends target middle) :
    Extends target source := by
  constructor
  · intro name args body found
    exact second.functions name args body (first.functions name args body found)
  · intro name values result absent found
    rcases first.libraries name values result absent found with ⟨absent, found⟩
    exact second.libraries name values result absent found

theorem Extends.libraryFunction_eq (extension : Extends target source)
    {implementation : List Constant → Except ExceptionObject Constant}
    (absent : findFunctionIn source.body name = none)
    (found : libraryFunction source name = some implementation) :
    findFunctionIn target.body name = none ∧ libraryFunction target name = some implementation := by
  have sourceCall (values) : libraryCall source name values = some (implementation values) := by
    simp [libraryCall, found]
  obtain ⟨noFunction, initial⟩ := extension.libraries name [] _ absent (sourceCall [])
  refine ⟨noFunction, ?_⟩
  cases targetFunction : libraryFunction target name with
  | none => simp [libraryCall, targetFunction] at initial
  | some other =>
      have same : other = implementation := by
        funext values
        have preserved := (extension.libraries name values _ absent (sourceCall values)).2
        simpa [libraryCall, targetFunction] using preserved
      simp [same]

def functionNames : List Stmt → List String
  | [] => []
  | .functionDef name _ _ _ :: rest => name :: functionNames rest
  | _ :: rest => functionNames rest

def importNames : List Stmt → List String
  | [] => []
  | .importFrom _ names :: rest => names.map Prod.snd ++ importNames rest
  | .importModules names :: rest => (moduleImports names).map Prod.snd ++ importNames rest
  | _ :: rest => importNames rest

private theorem findFunctionIn_append (prelude suffix : List Stmt) (name : String) :
    findFunctionIn (prelude ++ suffix) name =
      (findFunctionIn prelude name).orElse (fun _ => findFunctionIn suffix name) := by
  induction prelude with
  | nil => rfl
  | cons head tail ih =>
      cases head <;> simp only [List.cons_append, findFunctionIn]
      all_goals first | exact ih | split <;> simp_all

private theorem function_found (body : List Stmt) (name : String) :
    (findFunctionIn body name).isSome = true ↔ name ∈ functionNames body := by
  induction body with
  | nil => simp [findFunctionIn, functionNames]
  | cons head tail ih =>
      cases head <;> simp only [findFunctionIn, functionNames]
      all_goals first | exact ih | split <;> simp_all

private theorem importedFunction_append (prelude suffix : List Stmt) (name : String) :
    importedFunction (prelude ++ suffix) name =
      (importedFunction prelude name).orElse (fun _ => importedFunction suffix name) := by
  induction prelude with
  | nil => rfl
  | cons head tail ih =>
      cases head <;> simp only [List.cons_append, importedFunction]
      all_goals first | exact ih | split <;> simp_all

private theorem find_binding {α : Type} (names : List (α × String)) (name : String) :
    (names.find? (fun entry => entry.2 == name)).isSome = true ↔ name ∈ names.map Prod.snd := by
  cases found : names.find? (fun entry => entry.2 == name) with
  | none =>
      have absent : name ∉ names.map Prod.snd := by
        intro member
        rcases List.mem_map.mp member with ⟨entry, member, equal⟩
        have rejected := List.find?_eq_none.mp found entry member
        simp [equal] at rejected
      simp [absent]
  | some entry =>
      have member := List.mem_of_find?_eq_some found
      have equal := List.find?_some found
      have present : name ∈ names.map Prod.snd :=
        List.mem_map.mpr ⟨entry, member, by simpa using equal⟩
      simp [present]

private theorem import_found (body : List Stmt) (name : String) :
    (importedFunction body name).isSome = true ↔ name ∈ importNames body := by
  induction body with
  | nil => simp [importedFunction, importNames]
  | cons head tail ih =>
      cases head <;> simp only [importedFunction, importNames]
      all_goals try exact ih
      · rename_i library names
        have binding := find_binding names name
        split <;> simp_all
      · rename_i names
        have binding := find_binding (moduleImports names) name
        split <;> simp_all

/-- Linking a fresh prelude preserves completed executions from the suffix.
The conditions mention finite name lists, so clients can discharge them by
computation without comparing function bodies or trusting an AST hash. -/
theorem Extends.prepend (prelude : List Stmt) (source : Module)
    (freshFunctions : ∀ ⦃name⦄, name ∈ functionNames prelude →
      name ∈ functionNames source.body ++ importNames source.body → False)
    (freshImports : ∀ ⦃name⦄, name ∈ importNames prelude → name ∈ importNames source.body → False) :
    Extends ⟨prelude ++ source.body⟩ source := by
  constructor
  · intro name args body found
    have member : name ∈ functionNames source.body := (function_found _ _).mp (by simp [found])
    have absent : findFunctionIn prelude name = none := by
      cases h : findFunctionIn prelude name with
      | none => rfl
      | some _ => exact False.elim (freshFunctions (name := name) ((function_found prelude name).mp (by simp [h])) (by simp [member]))
    simp [findFunctionIn_append, absent, found]
  · intro name values result absent found
    have member : name ∈ importNames source.body := by
      unfold libraryCall libraryFunction at found
      split at found <;> simp_all [← import_found]
    have noFunction : findFunctionIn prelude name = none := by
      cases h : findFunctionIn prelude name with
      | none => rfl
      | some _ => exact False.elim (freshFunctions (name := name) ((function_found prelude name).mp (by simp [h])) (by simp [member]))
    have noImport : importedFunction prelude name = none := by
      cases h : importedFunction prelude name with
      | none => rfl
      | some _ => exact False.elim (freshImports (name := name) ((import_found prelude name).mp (by simp [h])) member)
    constructor
    · simp [findFunctionIn_append, noFunction, absent]
    · simpa [libraryCall, libraryFunction, importedFunction_append, noImport] using found

theorem Extends.step_eq (extension : Extends target source) (state : State)
    (supported : step source state ≠ .unsupported) :
    step target state = step source state := by
  rcases state with ⟨work, stack⟩
  cases work with
  | invoke name values =>
      cases found : findFunctionIn source.body name with
      | some declaration =>
          rcases declaration with ⟨args, body⟩
          simp only [step, found, extension.functions name args body found]
      | none =>
          cases library : libraryCall source name values with
          | none => simp [step, found, library, outcome] at supported
          | some result =>
              rcases extension.libraries name values result found library with ⟨absent, same⟩
              simp only [step, found, absent, library, same]
  | expr _ _ => rfl
  | block _ _ => rfl
  | value _ => rfl
  | startRange _ _ _ _ _ _ => rfl
  | startSum _ _ _ _ _ => rfl
  | sumLoop _ _ _ => rfl
  | primitive _ _ => rfl

theorem Reaches.extend (run : Reaches source initial final) (extension : Extends target source) :
    Reaches target initial final := by
  induction run with
  | refl => exact .refl
  | next transition _ ih =>
      apply Reaches.next _ ih
      rw [extension.step_eq _ (by simp [transition])]
      exact transition

theorem ReturnsValue.extend (result : ReturnsValue source name values value)
    (extension : Extends target source) : ReturnsValue target name values value :=
  fun stack => (result stack).extend extension

/-- Transfer finite exceptional executions too. This deliberately makes no
equivalence claim for unsupported executions of the source module. -/
theorem finishes_extend (run : Finishes (step source) initial result)
    (extension : Extends target source) : Finishes (step target) initial result := by
  induction run with
  | done transition =>
      apply Finishes.done
      rw [extension.step_eq _ (by simp [transition])]
      exact transition
  | next transition _ ih =>
      apply Finishes.next _ ih
      rw [extension.step_eq _ (by simp [transition])]
      exact transition

end FormalSW.PyAst.Calls
