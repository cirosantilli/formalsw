import lang.py.FormalSW.EvaluationRelocation

/-! List and tuple arithmetic preserves aliases across different allocation layouts. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

/-- List concatenation always allocates, including when either operand is empty. -/
theorem binary_add_lists_eval (heap : Heap) (left right : Nat) (xs ys : List Value)
    (first : heap[left]? = some (.list xs)) (second : heap[right]? = some (.list ys)) :
    Mutable.binary .add (.ref left) (.ref right) heap = Mutable.allocate (xs ++ ys) heap := by
  simp [Mutable.binary, show (BinOp.add == BinOp.add) = true from rfl, first, second, Mutable.array]

/-- Tuple concatenation reuses an operand when the other tuple is empty. -/
theorem binary_add_tuples_eval (heap : Heap) (left right : Nat) (xs ys : List Value)
    (first : heap[left]? = some (.tuple xs)) (second : heap[right]? = some (.tuple ys)) :
    Mutable.binary .add (.ref left) (.ref right) heap =
      (if xs.isEmpty then pure (.ref right) else if ys.isEmpty then pure (.ref left)
        else Mutable.allocateTuple (xs ++ ys) : Eval Value) heap := by
  simp [Mutable.binary, show (BinOp.add == BinOp.add) = true from rfl, first, second]

/-- Negative repetition counts produce empty lists, without a search cutoff. -/
theorem binary_mult_list_eval (heap : Heap) (address : Nat) (items : List Value) (count : Int)
    (found : heap[address]? = some (.list items)) :
    Mutable.binary .mult (.ref address) (.scalar (.int count)) heap =
      Mutable.allocate (List.replicate count.toNat items).flatten heap := by
  simp [Mutable.binary, show (BinOp.mult == BinOp.mult) = true from rfl, found, Mutable.array]

theorem binary_mult_tuple_eval (heap : Heap) (address : Nat) (items : List Value) (count : Int)
    (found : heap[address]? = some (.tuple items)) :
    Mutable.binary .mult (.ref address) (.scalar (.int count)) heap =
      (if count = 1 ∨ items.isEmpty then pure (.ref address)
        else Mutable.allocateTuple (List.replicate count.toNat items).flatten : Eval Value) heap := by
  simp [Mutable.binary, show (BinOp.mult == BinOp.mult) = true from rfl, found]

theorem binary_mult_ref_comm (heap : Heap) (address : Nat) (count : Int) :
    Mutable.binary .mult (.scalar (.int count)) (.ref address) heap =
      Mutable.binary .mult (.ref address) (.scalar (.int count)) heap := by
  simp only [Mutable.binary, show (BinOp.mult == BinOp.mult) = true from rfl, if_true]

variable {logical physical : Heap} {rename : Nat → Nat}

theorem ExecutionLayout.binary_add_lists (layout : ExecutionLayout logical physical rename)
    (left right : Nat) (xs ys : List Value)
    (first : logical[left]? = some (.list xs)) (second : logical[right]? = some (.list ys)) :
    EvalRelocates logical physical rename (Mutable.binary .add (.ref left) (.ref right))
      (Mutable.binary .add (.ref (rename left)) (.ref (rename right))) := by
  have firstInside : ∀ value ∈ xs, value.edge.Within logical.length := layout.closed _ (List.mem_of_getElem? first)
  have secondInside : ∀ value ∈ ys, value.edge.Within logical.length := layout.closed _ (List.mem_of_getElem? second)
  apply (layout.allocate_list_relocates (xs ++ ys) (by
    intro value member
    rcases List.mem_append.mp member with member | member
    · exact firstInside value member
    · exact secondInside value member)).congr (binary_add_lists_eval logical left right xs ys first second)
  simpa only [List.map_append] using binary_add_lists_eval physical (rename left) (rename right)
    (xs.map (relocateValue rename)) (ys.map (relocateValue rename)) (layout.runtime.lookup _ _ first)
    (layout.runtime.lookup _ _ second)

theorem ExecutionLayout.binary_add_tuples (layout : ExecutionLayout logical physical rename)
    (left right : Nat) (xs ys : List Value)
    (first : logical[left]? = some (.tuple xs)) (second : logical[right]? = some (.tuple ys)) :
    EvalRelocates logical physical rename (Mutable.binary .add (.ref left) (.ref right))
      (Mutable.binary .add (.ref (rename left)) (.ref (rename right))) := by
  have firstInside : ∀ value ∈ xs, value.edge.Within logical.length := layout.closed _ (List.mem_of_getElem? first)
  have secondInside : ∀ value ∈ ys, value.edge.Within logical.length := layout.closed _ (List.mem_of_getElem? second)
  have source := binary_add_tuples_eval logical left right xs ys first second
  have target := binary_add_tuples_eval physical (rename left) (rename right)
    (xs.map (relocateValue rename)) (ys.map (relocateValue rename)) (layout.runtime.lookup _ _ first)
    (layout.runtime.lookup _ _ second)
  by_cases emptyFirst : xs.isEmpty = true
  · apply (layout.pure_relocates (.ref right) (List.getElem?_eq_some_iff.mp second).1).congr
    · simpa only [emptyFirst, if_true] using source
    · simpa only [List.isEmpty_map, emptyFirst, if_true, relocateValue] using target
  · by_cases emptySecond : ys.isEmpty = true
    · apply (layout.pure_relocates (.ref left) (List.getElem?_eq_some_iff.mp first).1).congr
      · simpa only [emptyFirst, emptySecond, if_false, if_true] using source
      · simpa only [List.isEmpty_map, emptyFirst, emptySecond, if_false, if_true, relocateValue] using target
    · apply (layout.allocateTuple_relocates (xs ++ ys) (by
        intro value member
        rcases List.mem_append.mp member with member | member
        · exact firstInside value member
        · exact secondInside value member)).congr
      · simpa only [emptyFirst, emptySecond, if_false] using source
      · simpa only [List.isEmpty_map, emptyFirst, emptySecond, if_false, List.map_append] using target

theorem ExecutionLayout.binary_mult_list (layout : ExecutionLayout logical physical rename)
    (address : Nat) (items : List Value) (count : Int) (found : logical[address]? = some (.list items)) :
    EvalRelocates logical physical rename (Mutable.binary .mult (.ref address) (.scalar (.int count)))
      (Mutable.binary .mult (.ref (rename address)) (.scalar (.int count))) := by
  apply (layout.allocate_list_relocates _ (replicated_values_within _ count.toNat items
    (layout.closed _ (List.mem_of_getElem? found)))).congr (binary_mult_list_eval logical address items count found)
  simpa only [map_replicated_values] using binary_mult_list_eval physical (rename address)
    (items.map (relocateValue rename)) count (layout.runtime.lookup _ _ found)

theorem ExecutionLayout.binary_mult_tuple (layout : ExecutionLayout logical physical rename)
    (address : Nat) (items : List Value) (count : Int) (found : logical[address]? = some (.tuple items)) :
    EvalRelocates logical physical rename (Mutable.binary .mult (.ref address) (.scalar (.int count)))
      (Mutable.binary .mult (.ref (rename address)) (.scalar (.int count))) := by
  have source := binary_mult_tuple_eval logical address items count found
  have target := binary_mult_tuple_eval physical (rename address) (items.map (relocateValue rename)) count
    (layout.runtime.lookup _ _ found)
  by_cases reuse : count = 1 ∨ items.isEmpty = true
  · apply (layout.pure_relocates (.ref address) (List.getElem?_eq_some_iff.mp found).1).congr
    · simpa only [reuse, if_true] using source
    · simpa only [List.isEmpty_map, reuse, if_true, relocateValue] using target
  · apply (layout.allocateTuple_relocates _ (replicated_values_within _ count.toNat items
      (layout.closed _ (List.mem_of_getElem? found)))).congr
    · simpa only [reuse, if_false] using source
    · simpa only [List.isEmpty_map, reuse, if_false, map_replicated_values] using target

/-- Reversing the operands of builtin sequence repetition preserves the same allocation proof. -/
theorem EvalRelocates.mult_ref_comm (address : Nat) (count : Int)
    (related : EvalRelocates logical physical rename
      (Mutable.binary .mult (.ref address) (.scalar (.int count)))
      (Mutable.binary .mult (.ref (rename address)) (.scalar (.int count)))) :
    EvalRelocates logical physical rename (Mutable.binary .mult (.scalar (.int count)) (.ref address))
      (Mutable.binary .mult (.scalar (.int count)) (.ref (rename address))) :=
  related.congr (binary_mult_ref_comm logical address count) (binary_mult_ref_comm physical (rename address) count)

end FormalSW.PyAst.Mutable.Relocation
