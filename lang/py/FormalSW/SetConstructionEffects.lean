import lang.py.FormalSW.BinaryEffects
import lang.py.FormalSW.SetFromRelocation

/-! Set insertion retains existing cells even when hashing or a later insertion fails. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

theorem HeapGrows.hashKey (value : Value) : HeapGrows (Mutable.hashKey value) := by
  intro heap outcome after executed
  cases resolved : Mutable.keyOf heap value <;> simp [Mutable.hashKey, resolved] at executed
  rcases executed with ⟨rfl, rfl⟩
  exact Nat.le_refl _

theorem HeapGrows.mapM {α β : Type} (items : List α) (action : α → Eval β)
    (grows : ∀ item ∈ items, HeapGrows (action item)) : HeapGrows (items.mapM action) := by
  induction items with
  | nil => exact HeapGrows.pure []
  | cons item rest ih =>
    rw [List.mapM_cons]
    apply HeapGrows.bind (grows item (by simp))
    intro value
    apply HeapGrows.bind (ih (fun item member => grows item (by simp [member])))
    intro values
    exact HeapGrows.pure _

theorem HeapGrows.addItem (address : Nat) (value : Value) : HeapGrows (Mutable.addItem address value) := by
  unfold Mutable.addItem
  with_reducible repeat' first
    | exact HeapGrows.pure _
    | exact HeapGrows.error _
    | exact HeapGrows.unsupported
    | apply HeapGrows.bind HeapGrows.get; intro heap
    | apply HeapGrows.bind (HeapGrows.hashKey _); intro key
    | apply HeapGrows.bind (HeapGrows.modify _ (by intro heap; simp)); intro ignored
    | split

theorem HeapGrows.setKey (value : Value) : HeapGrows (Mutable.setKey value) := by
  unfold Mutable.setKey
  with_reducible repeat' first
    | exact HeapGrows.pure _
    | exact HeapGrows.error _
    | exact HeapGrows.unsupported
    | apply HeapGrows.bind HeapGrows.get; intro heap
    | split

theorem HeapGrows.allocateSetValues (items : List Value) : HeapGrows (Mutable.allocateSetValues items) := by
  rw [allocateSetValues_eq]
  split
  · apply HeapGrows.bind (HeapGrows.mapM items Mutable.setKey (fun item _ => HeapGrows.setKey item))
    intro keys
    exact HeapGrows.allocateSet _
  · apply HeapGrows.bind HeapGrows.get
    intro heap
    apply HeapGrows.bind (HeapGrows.allocateSet [])
    intro ignored
    apply HeapGrows.bind (HeapGrows.mapM items (Mutable.addItem heap.length) (fun item _ => HeapGrows.addItem _ item))
    intro values
    exact HeapGrows.pure _

end FormalSW.PyAst.Mutable.Relocation
