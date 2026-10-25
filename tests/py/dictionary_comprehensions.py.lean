import «.formalsw».tests.py.«dictionary_comprehensions.py.ast»
import lang.py.FormalSW.ComprehensionCalls
import lang.py.FormalSW.DictionaryCalls

/-! Install alongside tests/py/dictionary_comprehensions.py. The source proof
covers arbitrary signed elements and offsets, including repeated input keys. -/
namespace tests.py.dictionary_comprehensions
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
set_option Elab.async false

private abbrev program := DictionaryComprehensionsAst.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev encode (values : List Int) : List Mutable.Value := values.map number
private abbrev keyExpression : Expr := .name "value"
private abbrev valueExpression : Expr := .binOp (.name "value") .add (.name "offset")
private abbrev generators : List (Expr × Expr × List Expr) := [(.name "value", .name "values", [])]
private abbrev body (address : Nat) : List Stmt :=
  [.comprehensionStore address keyExpression valueExpression]

def update (offset : Int) (entries : List (Constant × Mutable.Value)) (value : Int) :
    List (Constant × Mutable.Value) :=
  ScalarDict.insert entries (.int value) (number (value + offset))

/-- ScalarDict.insert replaces in place, retaining the first key position.
Thus this fold specifies both iteration order and replacement semantics. -/
def entries (values : List Int) (offset : Int) : List (Constant × Mutable.Value) :=
  values.foldl (update offset) []

private theorem store (heap : Mutable.Heap) (collected : List (Constant × Mutable.Value))
    (env : Mutable.Env) (value offset : Int)
    (getValue : env "value" = some (number value))
    (getOffset : env "offset" = some (number offset)) (globals : Mutable.Globals) :
    BlockContinues program env (body heap.length) (heap ++ [.dict collected]) env
      (heap ++ [.dict (update offset collected value)]) globals := by
  have calculated : Evaluates program env valueExpression (heap ++ [.dict collected])
      (number (value + offset)) (heap ++ [.dict collected]) globals := by
    exact Evaluates.binary (Evaluates.lookup getValue) (Evaluates.lookup getOffset) rfl
  have inserted := Mutable.setItem_dictionary (heap ++ [.dict collected]) heap.length collected
    (by simp) (.int value) (number (value + offset))
  apply BlockContinues.comprehension_store
    (.cons (Evaluates.lookup getValue) (.cons calculated .nil))
  simpa [update, List.set_append_right] using inserted

private theorem loop (heap : Mutable.Heap) (address : Nat) (values remaining : List Int)
    (found : heap[address]? = some (.list (encode values))) (position : Nat)
    (suffix : values.drop position = remaining) (offset : Int)
    (collected : List (Constant × Mutable.Value)) (env : Mutable.Env)
    (getOffset : env "offset" = some (number offset)) (globals : Mutable.Globals) :
    ∃ finalEnv, BlockContinues program env
      [.sequenceStepLoop "value" (.ref address) position (body heap.length) []]
      (heap ++ [.dict collected]) finalEnv
      (heap ++ [.dict (remaining.foldl (update offset) collected)]) globals := by
  have inside : address < heap.length := (List.getElem?_eq_some_iff.mp found).1
  have sequence (collected : List (Constant × Mutable.Value)) :
      Mutable.sequence (.ref address) (heap ++ [.dict collected]) =
        some (.ok (encode values), heap ++ [.dict collected]) := by
    simp [Mutable.sequence, List.getElem?_append_left inside, found]
  induction remaining generalizing position collected env with
  | nil =>
      refine ⟨env, ?_⟩
      apply BlockContinues.sequence_done (items := encode values)
        (by simpa only [sequenceValue] using sequence collected)
      · have missing : values[position]? = none := by
          simpa only [suffix, List.head?_nil] using (List.head?_drop (l := values) (i := position)).symm
        simp only [encode, List.getElem?_map, missing, Option.map_none]
      · exact BlockContinues.nil
  | cons value rest ih =>
      let bound := setLocal env "value" (number value)
      have emitted := store heap collected bound value offset (by simp [bound, setLocal])
        (by simpa [bound, setLocal] using getOffset) globals
      obtain ⟨finalEnv, continued⟩ := ih (position + 1)
        (by simp only [List.drop_add_one_eq_tail_drop, suffix, List.tail_cons])
        (update offset collected value) bound (by simpa [bound, setLocal] using getOffset)
      refine ⟨finalEnv, ?_⟩
      have item : values[position]? = some value := by
        simpa only [suffix, List.head?_cons] using (List.head?_drop (l := values) (i := position)).symm
      apply BlockContinues.sequence_step (items := encode values) (value := number value)
        (by simpa only [sequenceValue] using sequence collected)
        (by simp only [encode, List.getElem?_map, item, Option.map_some])
      simpa only [Calls.loopContinuation, body, Calls.loopControl, Calls.loopControlStmt,
        Bool.false_or, Bool.false_eq_true, if_false, List.foldl_cons] using emitted.append continued

/-- The actual comprehension allocates exactly one fresh dictionary and retains
all caller objects, independently of the list's length and key repetitions. -/
theorem shifted.result (values : List Int) (offset : Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (encode values))) (globals : Mutable.Globals := []) :
    ReturnsValue program "shifted" [.ref address, number offset] heap (.ref heap.length)
      (heap ++ [.dict (entries values offset)]) globals := by
  let params := ((findFunctionIn program.body "shifted").getD ([], [])).1
  let functionBody := ((findFunctionIn program.body "shifted").getD ([], [])).2
  let initial := functionEnv params functionBody [.ref address, number offset] globals
  let masked := comprehensionTargetsEnv initial generators
  have getOffset : masked "offset" = some (number offset) := by
    have unmasked : generators.any (fun generator => (targetLocals generator.1).contains "offset") = false := by simp [generators, targetLocals]
    simp only [masked, comprehensionTargetsEnv, unmasked, Bool.false_eq_true, if_false]
    cases globals <;> rfl
  obtain ⟨finalEnv, executed⟩ := loop heap address values values found 0 rfl offset [] masked getOffset globals
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.dict_comp_sequence (receiver := .ref address) (items := encode values)
    (middle := heap) (finalEnv := finalEnv)
    (by intro expressions impossible; cases impossible)
    (by intro expressions impossible; cases impossible)
    (by intro expressions impossible; cases impossible)
    (Evaluates.lookup (by cases globals <;> rfl))
    (by simp [Mutable.sequence, found])
  simpa only [generators, comprehensionTargetName, comprehensionTargetBody, comprehensionFilters,
    List.foldr_nil, comprehensionTargetsBody, sequenceSource, entries, masked, initial, params,
    functionBody, body, keyExpression, valueExpression] using executed

theorem shifted.«Returns» (heap : Mutable.Heap) (address : Nat) (offset : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "shifted" [.ref address, number offset] heap).Returns := by
  obtain ⟨values, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (shifted.result values offset heap address found).returns

theorem shifted.«Supported» (heap : Mutable.Heap) (address : Nat) (offset : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "shifted" [.ref address, number offset] heap).Supported :=
  (shifted.«Returns» heap address offset valid typed).supported

/-- A duplicate keeps its original position, rather than moving to the end. -/
example (offset : Int) : entries [4, -2, 4, 3, -2] offset =
    [(.int 4, number (4 + offset)), (.int (-2), number (-2 + offset)), (.int 3, number (3 + offset))] := by
  rfl

/-- Replacement really writes the latest value, even if the previous value
was different. The source loop uses this same insertion operation. -/
example : ScalarDict.insert [(.int 4, number 0), (.int (-2), number 5)] (.int 4) (number 99) =
    [(.int 4, number 99), (.int (-2), number 5)] := by rfl

end tests.py.dictionary_comprehensions
