import lang.py.FormalSW.GraphPreservation

/-! The actual snapshot comparator's seen-reference search, with relocated addresses. -/
namespace FormalSW.PyAst.Graph.Relocation
open DataProof
attribute [local simp] Except.bind Except.map Except.pure Int.natCast_inj

private def item (name : String) (index : Int) : Expr := .subscript (.name name) (.constant (.int index))
private def indexed (name index : String) : Expr := .subscript (.name name) (.name index)
private def length (name : String) : Expr := .builtinCall .len [.name name]
private def falseReturn : List Stmt := [.return (.constant (.bool false))]

private def seenBody : List Stmt := [
  .ifThen (.compare (item "a" 1) [(.eq, indexed "seen_left" "index")]) [
    .ifThen (.compare (item "b" 1) [(.notEq, indexed "seen_right" "index")]) falseReturn [],
    .assign [.name "found"] (.constant (.bool true))] [
    .ifThen (.compare (item "b" 1) [(.eq, indexed "seen_right" "index")]) falseReturn []],
  .assign [.name "index"] (.binOp (.name "index") .add (.constant (.int 1)))]

def seenLoop : Stmt :=
  .whileDo (.compare (.name "index") [(.lt, length "seen_left")]) seenBody []


private def expandBody : List Stmt := [
  .assign [.name "seen_left"] (.binOp (.name "seen_left") .add (.list [item "a" 1])),
  .assign [.name "seen_right"] (.binOp (.name "seen_right") .add (.list [item "b" 1])),
  .assign [.name "node_left"] (.subscript (item "left" 1) (item "a" 1)),
  .assign [.name "node_right"] (.subscript (item "right" 1) (item "b" 1)),
  .ifThen (.compare (item "node_left" 0) [(.notEq, item "node_right" 0)]) falseReturn [],
  .ifThen (.compare (item "node_left" 1) [(.notEq, item "node_right" 1)]) falseReturn [],
  .ifThen (.compare (.builtinCall .len [item "node_left" 2])
    [(.notEq, .builtinCall .len [item "node_right" 2])]) falseReturn [],
  .assign [.name "pending_left"] (.binOp (.name "pending_left") .add (item "node_left" 2)),
  .assign [.name "pending_right"] (.binOp (.name "pending_right") .add (item "node_right" 2))]

private def referenceBody : List Stmt := [
  .assign [.name "found"] (.constant (.bool false)),
  .assign [.name "index"] (.constant (.int 0)),
  seenLoop,
  .ifThen (.unaryOp .not (.name "found")) expandBody []]

private def graphBody : List Stmt := [
  .assign [.name "a"] (indexed "pending_left" "cursor"),
  .assign [.name "b"] (indexed "pending_right" "cursor"),
  .ifThen (.compare (item "a" 0) [(.notEq, item "b" 0)]) falseReturn [],
  .ifThen (.compare (item "a" 0) [(.eq, .constant (.string "ref"))]) referenceBody
    [.ifThen (.compare (item "a" 1) [(.notEq, item "b" 1)]) falseReturn []],
  .assign [.name "cursor"] (.binOp (.name "cursor") .add (.constant (.int 1)))]

private def graphLoop : Stmt :=
  .whileDo (.compare (.name "cursor") [(.lt, length "pending_left")]) graphBody []

/-- Keep the proof decomposition tied to the checked Python source. -/
private theorem source_body : findFunctionIn source.body "same_snapshot" = some
    ([{ name := "left", annotation := none }, { name := "right", annotation := none }], [
      .ifThen (.compare (.call (.name "type") [.name "left"])
        [(.notEq, .call (.name "type") [.name "right"])]) falseReturn [],
      .ifThen (.compare (.call (.name "type") [.name "left"]) [(.notEq, .name "list")])
        [.return (.compare (.name "left") [(.eq, .name "right")])] [],
      .assign [.name "pending_left"] (item "left" 0),
      .assign [.name "pending_right"] (item "right" 0),
      .ifThen (.compare (length "pending_left") [(.notEq, length "pending_right")]) falseReturn [],
      .assign [.name "seen_left"] (.list []),
      .assign [.name "seen_right"] (.list []),
      .assign [.name "cursor"] (.constant (.int 0)),
      graphLoop,
      .return (.constant (.bool true))]) := by rfl


private def extractedSeenLoop : Option Stmt :=
  match (((findFunctionIn source.body "same_snapshot").getD ([], [])).2[8]? : Option Stmt) with
  | some (.whileDo _ body _) => match (body[3]? : Option Stmt) with
      | some (.ifThen _ yes _) => yes[2]?
      | _ => none
  | _ => none

theorem seenLoop_source : extractedSeenLoop = some seenLoop := rfl

/-- Addresses need only be injective on the finite reachable domain. -/
def InjectiveBelow (rename : Nat → Nat) (limit : Nat) : Prop :=
  ∀ i < limit, ∀ j < limit, rename i = rename j → i = j

def addresses (rename : Nat → Nat) (count : Nat) : List Data :=
  (List.range count).map fun (index : Nat) => .scalar (.int (rename index))

private theorem eval_compare_int (left : dataExpr env a = some (.ok (.scalar (.int x))))
    (right : dataExpr env b = some (.ok (.scalar (.int y)))) :
    dataExpr env (.compare a [(op, b)]) = some (.ok (.scalar (.bool (evalCmpOp op x y)))) := by
  cases op <;> simp [bind, pure, dataExpr, left, right, Data.equal, scalarCompare, evalCmpOp]

private theorem reference_index (found : env name = some (Edge.ref address).encode) :
    dataExpr env (item name 1) = some (.ok (.scalar (.int address))) := by
  simp [bind, pure, dataExpr, item, found, Edge.encode]


private theorem seen_index {count position : Nat} (rename : Nat → Nat)
    (found : env name = some (.list (addresses rename count)))
    (index : env "index" = some (.scalar (.int position))) (valid : position < count) :
    dataExpr env (indexed name "index") = some (.ok (.scalar (.int (rename position)))) := by
  apply DataProof.getItem (items := addresses rename count) (position := position)
    (by simp [dataExpr, found]) (by simp [dataExpr, index]) (by omega)
  simp [addresses, valid]

/-- Searching the two relocated seen tables recognizes the same logical
reference. Distinct logical addresses cannot be silently merged into aliases. -/
theorem seen_result (env : DataEnv) (leftMap rightMap : Nat → Nat) (limit address count position : Nat)
    (leftInjective : InjectiveBelow leftMap limit) (rightInjective : InjectiveBelow rightMap limit)
    (addressBound : address < limit) (countBound : count ≤ limit)
    (left : env "a" = some (Edge.ref (leftMap address)).encode)
    (right : env "b" = some (Edge.ref (rightMap address)).encode)
    (seenLeft : env "seen_left" = some (.list (addresses leftMap count)))
    (seenRight : env "seen_right" = some (.list (addresses rightMap count)))
    (index : env "index" = some (.scalar (.int position)))
    (found : env "found" = some (.scalar (.bool (decide (address < position)))))
    (bounded : position ≤ count) :
    ∃ finalEnv, BlockContinues env [seenLoop] finalEnv ∧
      finalEnv "found" = some (.scalar (.bool (decide (address < count)))) ∧
      ∀ name, name ≠ "index" → name ≠ "found" → finalEnv name = env name := by
  by_cases valid : position < count
  · let flagEnv := if address = position then env.set "found" (.scalar (.bool true)) else env
    have step : BlockContinues env [seenBody[0]'(by decide)] flagEnv := by
      by_cases equal : address = position
      · apply BlockContinues.branch (flag := true)
        · simpa [evalCmpOp, equal] using eval_compare_int (op := .eq) (reference_index left) (seen_index leftMap seenLeft index valid)
        · apply BlockContinues.append (body := [.ifThen (.compare (item "b" 1)
            [(.notEq, indexed "seen_right" "index")]) falseReturn []])
          · exact BlockContinues.branch
              (by simpa [evalCmpOp, equal] using eval_compare_int (op := .notEq) (reference_index right) (seen_index rightMap seenRight index valid)) BlockContinues.nil
          · simpa only [flagEnv, if_pos equal] using
              (BlockContinues.assign (env := env) (name := "found")
                (show dataExpr env (.constant (.bool true)) = some (.ok (.scalar (.bool true))) from by simp [dataExpr]))
      · have differentLeft : leftMap address ≠ leftMap position := by
          intro same
          exact equal (leftInjective address addressBound position (by omega) same)
        have differentRight : rightMap address ≠ rightMap position := by
          intro same
          exact equal (rightInjective address addressBound position (by omega) same)
        apply BlockContinues.branch (flag := false)
        · simpa [evalCmpOp, differentLeft] using eval_compare_int (op := .eq) (reference_index left) (seen_index leftMap seenLeft index valid)
        · simpa only [flagEnv, if_neg equal] using BlockContinues.branch (flag := false)
            (by simpa [evalCmpOp, differentRight] using eval_compare_int (op := .eq) (reference_index right) (seen_index rightMap seenRight index valid)) BlockContinues.nil
    have kept : ∀ name, name ≠ "found" → flagEnv name = env name := by
      intro name different
      by_cases equal : address = position <;> simp [flagEnv, equal, DataEnv.set, different]
    have nextFound : flagEnv "found" = some (.scalar (.bool (decide (address < position + 1)))) := by
      by_cases equal : address = position
      · simp [flagEnv, equal, DataEnv.set]
      · have same : (address < position + 1) = (address < position) := propext (by omega)
        simpa [flagEnv, equal, same] using found
    let nextEnv := flagEnv.set "index" (.scalar (.int (position + 1 : Nat)))
    obtain ⟨finalEnv, rest, result, unchanged⟩ := seen_result nextEnv leftMap rightMap limit address count (position + 1)
      leftInjective rightInjective addressBound countBound
      (by simpa [nextEnv, DataEnv.set, kept] using left)
      (by simpa [nextEnv, DataEnv.set, kept] using right)
      (by simpa [nextEnv, DataEnv.set, kept] using seenLeft)
      (by simpa [nextEnv, DataEnv.set, kept] using seenRight)
      (by simp [nextEnv, DataEnv.set]) (by simpa [nextEnv, DataEnv.set] using nextFound) (by omega)
    refine ⟨finalEnv, ?_, result, ?_⟩
    · apply BlockContinues.while_loop (flag := true)
      · simp [bind, pure, dataExpr, length, index, seenLeft, addresses, scalarCompare, evalCmpOp, valid]
      · apply BlockContinues.append step
        apply BlockContinues.append (body := [.assign [.name "index"]
          (.binOp (.name "index") .add (.constant (.int 1)))])
        · exact BlockContinues.assign (value := .scalar (.int (position + 1 : Nat)))
            (by simp [bind, pure, dataExpr, kept, index, scalarBinary])
        · exact rest
    · intro name notIndex notFound
      rw [unchanged name notIndex notFound]
      simp [nextEnv, DataEnv.set, notIndex, kept, notFound]
  · refine ⟨env, ?_, ?_, ?_⟩
    · apply BlockContinues.while_loop (flag := false)
      · simp [bind, pure, dataExpr, length, index, seenLeft, addresses, scalarCompare, evalCmpOp, valid]
      · exact BlockContinues.nil
    · have same : position = count := by omega
      simpa [same] using found
    · intros; rfl
termination_by count - position


/-- Logical reference indices are translated independently in the two heaps. -/
def relocateEdge (rename : Nat → Nat) : Edge → Edge
  | .scalar value => .scalar value
  | .ref address => .ref (rename address)

def encodedEdges (rename : Nat → Nat) (edges : List Edge) : List Data :=
  edges.map (fun edge => (relocateEdge rename edge).encode)

structure LoopState (env : DataEnv) (left right : Data) (pending : List Edge)
    (leftMap rightMap : Nat → Nat) (seen cursor : Nat) : Prop where
  leftValue : env "left" = some left
  rightValue : env "right" = some right
  pendingLeft : env "pending_left" = some (.list (encodedEdges leftMap pending))
  pendingRight : env "pending_right" = some (.list (encodedEdges rightMap pending))
  seenLeft : env "seen_left" = some (.list (addresses leftMap seen))
  seenRight : env "seen_right" = some (.list (addresses rightMap seen))
  cursorValue : env "cursor" = some (.scalar (.int cursor))

structure EdgeState (env : DataEnv) (left right : Data) (pending : List Edge)
    (leftMap rightMap : Nat → Nat) (seen cursor : Nat) (edge : Edge) : Prop
    extends LoopState env left right pending leftMap rightMap seen cursor where
  a : env "a" = some (relocateEdge leftMap edge).encode
  b : env "b" = some (relocateEdge rightMap edge).encode

theorem read_edge (state : LoopState env left right pending leftMap rightMap seen cursor)
    (found : pending[cursor]? = some edge) :
    let finalEnv := (env.set "a" (relocateEdge leftMap edge).encode).set "b" (relocateEdge rightMap edge).encode
    BlockContinues env (graphBody.take 2) finalEnv ∧
      EdgeState finalEnv left right pending leftMap rightMap seen cursor edge := by
  dsimp only
  constructor
  · apply BlockContinues.append (body := [.assign [.name "a"] (indexed "pending_left" "cursor")])
    · apply BlockContinues.assign (value := (relocateEdge leftMap edge).encode)
      apply DataProof.getItem (items := encodedEdges leftMap pending) (position := cursor)
        (by simp [dataExpr, state.pendingLeft]) (by simp [dataExpr, state.cursorValue]) (by omega)
      simp [encodedEdges, found]
    · apply BlockContinues.assign (value := (relocateEdge rightMap edge).encode)
      apply DataProof.getItem (items := encodedEdges rightMap pending) (position := cursor)
        (by simp [dataExpr, DataEnv.set, state.pendingRight]) (by simp [dataExpr, DataEnv.set, state.cursorValue]) (by omega)
      simp [encodedEdges, found]
  · constructor
    · constructor <;> simp [DataEnv.set, state.leftValue, state.rightValue, state.pendingLeft,
        state.pendingRight, state.seenLeft, state.seenRight, state.cursorValue]
    · simp [DataEnv.set]
    · simp [DataEnv.set]

theorem advance (state : LoopState env left right pending leftMap rightMap seen cursor) :
    let finalEnv := env.set "cursor" (.scalar (.int (cursor + 1 : Nat)))
    BlockContinues env [.assign [.name "cursor"] (.binOp (.name "cursor") .add (.constant (.int 1)))] finalEnv ∧
      LoopState finalEnv left right pending leftMap rightMap seen (cursor + 1) := by
  dsimp only
  constructor
  · exact BlockContinues.assign (by simp [bind, pure, dataExpr, state.cursorValue, scalarBinary])
  · constructor <;> simp [DataEnv.set, state.leftValue, state.rightValue, state.pendingLeft,
      state.pendingRight, state.seenLeft, state.seenRight]

theorem search_reference (state : EdgeState env left right pending leftMap rightMap seen cursor (.ref address))
    (limit : Nat) (leftInjective : InjectiveBelow leftMap limit) (rightInjective : InjectiveBelow rightMap limit)
    (addressBound : address < limit) (seenBound : seen ≤ limit) :
    ∃ finalEnv, BlockContinues env (referenceBody.take 3) finalEnv ∧
      EdgeState finalEnv left right pending leftMap rightMap seen cursor (.ref address) ∧
      finalEnv "found" = some (.scalar (.bool (decide (address < seen)))) := by
  let initial := (env.set "found" (.scalar (.bool false))).set "index" (.scalar (.int 0))
  obtain ⟨finalEnv, searched, found, preserved⟩ := seen_result initial leftMap rightMap limit address seen 0
    leftInjective rightInjective addressBound seenBound
    (by simpa [initial, DataEnv.set, relocateEdge] using state.a)
    (by simpa [initial, DataEnv.set, relocateEdge] using state.b)
    (by simp [initial, DataEnv.set, state.seenLeft]) (by simp [initial, DataEnv.set, state.seenRight])
    (by simp [initial, DataEnv.set]) (by simp [initial, DataEnv.set]) (by omega)
  refine ⟨finalEnv, ?_, ?_, found⟩
  · apply BlockContinues.append (body := [.assign [.name "found"] (.constant (.bool false))])
      (BlockContinues.assign (value := .scalar (.bool false)) (by simp [dataExpr]))
    apply BlockContinues.append (body := [.assign [.name "index"] (.constant (.int 0))])
      (BlockContinues.assign (value := .scalar (.int 0)) (by simp [dataExpr]))
    exact searched
  · constructor
    · constructor <;> simp [preserved, initial, DataEnv.set, state.leftValue, state.rightValue,
        state.pendingLeft, state.pendingRight, state.seenLeft, state.seenRight, state.cursorValue]
    · simp [preserved, initial, DataEnv.set, state.a]
    · simp [preserved, initial, DataEnv.set, state.b]

private theorem tag_equal (state : EdgeState env left right pending leftMap rightMap seen cursor edge) :
    dataExpr env (.compare (item "a" 0) [(.notEq, item "b" 0)]) = some (.ok (.scalar (.bool false))) := by
  cases edge <;> simp [bind, pure, dataExpr, item, state.a, state.b, relocateEdge, Edge.encode, Data.equal_self]

theorem scalar_tail (state : EdgeState env left right pending leftMap rightMap seen cursor (.scalar value)) :
    ∃ finalEnv, BlockContinues env (graphBody.drop 2) finalEnv ∧
      LoopState finalEnv left right pending leftMap rightMap seen (cursor + 1) := by
  obtain ⟨increment, finalState⟩ := advance state.toLoopState
  refine ⟨_, ?_, finalState⟩
  apply BlockContinues.append (body := [.ifThen (.compare (item "a" 0) [(.notEq, item "b" 0)]) falseReturn []])
    (BlockContinues.branch (tag_equal state) BlockContinues.nil)
  apply BlockContinues.append (body := [.ifThen (.compare (item "a" 0) [(.eq, .constant (.string "ref"))])
    referenceBody [.ifThen (.compare (item "a" 1) [(.notEq, item "b" 1)]) falseReturn []]])
  · apply BlockContinues.branch (flag := false)
    · cases value <;> simp [bind, pure, dataExpr, item, state.a, relocateEdge, Edge.encode, Data.typeName, Data.equal, scalarCompare]
    · exact BlockContinues.branch (flag := false) (by
        simp [bind, pure, dataExpr, item, state.a, state.b, relocateEdge, Edge.encode, Data.equal_self]) BlockContinues.nil
  · exact increment

theorem known_tail (state : EdgeState env left right pending leftMap rightMap seen cursor (.ref address))
    (limit : Nat) (leftInjective : InjectiveBelow leftMap limit) (rightInjective : InjectiveBelow rightMap limit)
    (seenBound : seen ≤ limit) (known : address < seen) :
    ∃ finalEnv, BlockContinues env (graphBody.drop 2) finalEnv ∧
      LoopState finalEnv left right pending leftMap rightMap seen (cursor + 1) := by
  obtain ⟨searchEnv, searched, searchState, found⟩ :=
    search_reference state limit leftInjective rightInjective (by omega) seenBound
  obtain ⟨increment, finalState⟩ := advance searchState.toLoopState
  refine ⟨_, ?_, finalState⟩
  apply BlockContinues.append (body := [.ifThen (.compare (item "a" 0) [(.notEq, item "b" 0)]) falseReturn []])
    (BlockContinues.branch (tag_equal state) BlockContinues.nil)
  apply BlockContinues.append (body := [.ifThen (.compare (item "a" 0) [(.eq, .constant (.string "ref"))])
    referenceBody [.ifThen (.compare (item "a" 1) [(.notEq, item "b" 1)]) falseReturn []]])
  · apply BlockContinues.branch (flag := true)
    · simp [bind, pure, dataExpr, item, state.a, relocateEdge, Edge.encode, Data.equal, scalarCompare]
    · apply BlockContinues.append searched
      exact BlockContinues.branch (flag := false)
        (by simp [bind, pure, dataExpr, found, known, Data.truth, scalarTruth]) BlockContinues.nil
  · exact increment


def relocateNode (rename : Nat → Nat) (node : Node) : Node :=
  ⟨node.kind, node.labels, node.edges.map (relocateEdge rename)⟩

private theorem node_read {heap : Heap} {node : Node} (root : env name = some heap.encode)
    (reference : env referenceName = some (Edge.ref address).encode)
    (found : heap.nodes[address]? = some node) :
    dataExpr env (.subscript (item name 1) (item referenceName 1)) = some (.ok node.encode) := by
  apply DataProof.getItem (items := heap.nodes.map Node.encode) (position := address)
    (by simp [bind, pure, dataExpr, item, root, Heap.encode]) (reference_index reference) (by omega)
  simp [found]


theorem expand_reference (left right : Heap) (node : Node)
    (state : EdgeState env left.encode right.encode pending leftMap rightMap seen cursor (.ref seen))
    (leftNode : left.nodes[leftMap seen]? = some (relocateNode leftMap node))
    (rightNode : right.nodes[rightMap seen]? = some (relocateNode rightMap node)) :
    ∃ finalEnv, BlockContinues env expandBody finalEnv ∧
      LoopState finalEnv left.encode right.encode (pending ++ node.edges) leftMap rightMap (seen + 1) cursor := by
  let e1 := env.set "seen_left" (.list (addresses leftMap (seen + 1)))
  let e2 := e1.set "seen_right" (.list (addresses rightMap (seen + 1)))
  let e3 := e2.set "node_left" (relocateNode leftMap node).encode
  let e4 := e3.set "node_right" (relocateNode rightMap node).encode
  let e5 := e4.set "pending_left" (.list (encodedEdges leftMap (pending ++ node.edges)))
  let e6 := e5.set "pending_right" (.list (encodedEdges rightMap (pending ++ node.edges)))
  have addLeft : BlockContinues env [expandBody[0]'(by decide)] e1 := by
    apply BlockContinues.assign
    simp [bind, pure, Functor.map, dataExpr, item, state.a, state.seenLeft, relocateEdge,
      Edge.encode, addresses, List.range_succ, List.map_append]
  have addRight : BlockContinues e1 [expandBody[1]'(by decide)] e2 := by
    apply BlockContinues.assign
    simp [bind, pure, Functor.map, dataExpr, item, e1, DataEnv.set, state.b, state.seenRight,
      relocateEdge, Edge.encode, addresses, List.range_succ, List.map_append]
  have readLeft : BlockContinues e2 [expandBody[2]'(by decide)] e3 :=
    BlockContinues.assign (node_read (by simp [e2, e1, DataEnv.set, state.leftValue])
      (by simpa [e2, e1, DataEnv.set, relocateEdge] using state.a) leftNode)
  have readRight : BlockContinues e3 [expandBody[3]'(by decide)] e4 :=
    BlockContinues.assign (node_read (by simp [e3, e2, e1, DataEnv.set, state.rightValue])
      (by simpa [e3, e2, e1, DataEnv.set, relocateEdge] using state.b) rightNode)
  refine ⟨e6, ?_, ?_⟩
  · apply BlockContinues.append addLeft
    apply BlockContinues.append addRight
    apply BlockContinues.append readLeft
    apply BlockContinues.append readRight
    apply BlockContinues.append (body := [expandBody[4]'(by decide)])
    · apply BlockContinues.branch (flag := false)
      · simp [bind, pure, dataExpr, item, e4, e3, DataEnv.set, relocateNode, Node.encode, Data.equal_self]
      · exact BlockContinues.nil
    · apply BlockContinues.append (body := [expandBody[5]'(by decide)])
      · apply BlockContinues.branch (flag := false)
        · simp [bind, pure, dataExpr, item, e4, e3, DataEnv.set, relocateNode, Node.encode, Data.equal_self]
        · exact BlockContinues.nil
      · apply BlockContinues.append (body := [expandBody[6]'(by decide)])
        · apply BlockContinues.branch (flag := false)
          · simp [bind, pure, dataExpr, item, e4, e3, DataEnv.set, relocateNode, Node.encode, Data.equal_self]
          · exact BlockContinues.nil
        · apply BlockContinues.append (body := [expandBody[7]'(by decide)])
            (middle := e5)
          · apply BlockContinues.assign
            simp [bind, pure, dataExpr, item, e4, e3, e2, e1, DataEnv.set, relocateNode, Node.encode,
              state.pendingLeft, encodedEdges, List.map_append, List.map_map, Function.comp_def]
          · apply BlockContinues.assign
            simp [bind, pure, dataExpr, item, e5, e4, e3, e2, e1, DataEnv.set, relocateNode, Node.encode,
              state.pendingRight, encodedEdges, List.map_append, List.map_map, Function.comp_def]
  · constructor <;> simp [e6, e5, e4, e3, e2, e1, DataEnv.set, state.leftValue, state.rightValue, state.cursorValue]

theorem new_tail (left right : Heap) (node : Node)
    (state : EdgeState env left.encode right.encode pending leftMap rightMap seen cursor (.ref seen))
    (limit : Nat) (leftInjective : InjectiveBelow leftMap limit) (rightInjective : InjectiveBelow rightMap limit)
    (fresh : seen < limit)
    (leftNode : left.nodes[leftMap seen]? = some (relocateNode leftMap node))
    (rightNode : right.nodes[rightMap seen]? = some (relocateNode rightMap node)) :
    ∃ finalEnv, BlockContinues env (graphBody.drop 2) finalEnv ∧
      LoopState finalEnv left.encode right.encode (pending ++ node.edges) leftMap rightMap (seen + 1) (cursor + 1) := by
  obtain ⟨searchEnv, searched, searchState, found⟩ :=
    search_reference state limit leftInjective rightInjective fresh (by omega)
  obtain ⟨expandedEnv, expanded, expandedState⟩ := expand_reference left right node searchState leftNode rightNode
  obtain ⟨increment, finalState⟩ := advance expandedState
  refine ⟨_, ?_, finalState⟩
  apply BlockContinues.append (body := [.ifThen (.compare (item "a" 0) [(.notEq, item "b" 0)]) falseReturn []])
    (BlockContinues.branch (tag_equal state) BlockContinues.nil)
  apply BlockContinues.append (body := [.ifThen (.compare (item "a" 0) [(.eq, .constant (.string "ref"))])
    referenceBody [.ifThen (.compare (item "a" 1) [(.notEq, item "b" 1)]) falseReturn []]])
  · apply BlockContinues.branch (flag := true)
    · simp [bind, pure, dataExpr, item, state.a, relocateEdge, Edge.encode, Data.equal, scalarCompare]
    · apply BlockContinues.append searched
      exact BlockContinues.branch (flag := true)
        (by simp [bind, pure, dataExpr, found, Data.truth, scalarTruth]) expanded
  · exact increment


/-- A physical heap represents each logical node at its relocated address. -/
structure Layout (logical : List Node) (physical : Heap) (rename : Nat → Nat) : Prop where
  injective : InjectiveBelow rename logical.length
  lookup : ∀ index node, logical[index]? = some node →
    physical.nodes[rename index]? = some (relocateNode rename node)

private theorem within_mono {edge : Edge} {small large : Nat}
    (inside : edge.Within small) (bounded : small ≤ large) : edge.Within large := by
  cases edge with
  | scalar value => trivial
  | ref address => change address < large; change address < small at inside; omega

private theorem continue_loop (state : LoopState env left right pending leftMap rightMap seen cursor)
    (valid : cursor < pending.length) (body : BlockContinues env graphBody finalEnv)
    (rest : BlockReturns finalEnv [graphLoop, .return (.constant (.bool true))] (.scalar (.bool true))) :
    BlockReturns env [graphLoop, .return (.constant (.bool true))] (.scalar (.bool true)) := by
  apply BlockReturns.while_loop (flag := true)
  · simp [bind, pure, dataExpr, length, state.cursorValue, state.pendingLeft, encodedEdges, scalarCompare, evalCmpOp, valid]
  · exact body.returns rest

/-- After the caller's anchored prefix has been visited, fresh logical nodes
may be discovered in order. Each newly queued reference is at most the next
logical index; a finite node domain bounds all expansion. -/
theorem ordered_run (logical : List Node) (left right : Heap) (firstFresh : Nat)
    (leftLayout : Layout logical left leftMap) (rightLayout : Layout logical right rightMap)
    (closed : ∀ node ∈ logical, ∀ edge ∈ node.edges, edge.Within logical.length)
    (ordered : ∀ index node, firstFresh ≤ index → logical[index]? = some node →
      ∀ edge ∈ node.edges, edge.Within (index + 2))
    (state : LoopState env left.encode right.encode pending leftMap rightMap seen cursor)
    (seenAtLeast : firstFresh ≤ seen) (seenBound : seen ≤ logical.length)
    (pendingClosed : ∀ edge ∈ pending, edge.Within logical.length)
    (pendingNext : ∀ edge ∈ pending, edge.Within (seen + 1)) :
    BlockReturns env [graphLoop, .return (.constant (.bool true))] (.scalar (.bool true)) := by
  by_cases valid : cursor < pending.length
  · have found : pending[cursor]? = some pending[cursor] := List.getElem?_eq_getElem valid
    have member : pending[cursor] ∈ pending := List.getElem_mem valid
    obtain ⟨read, edgeState⟩ := read_edge state found
    cases edge : pending[cursor] with
    | scalar value =>
      simp only [edge] at read
      obtain ⟨finalEnv, tail, finalState⟩ := scalar_tail (value := value)
        (by simpa only [edge] using edgeState)
      have body : BlockContinues env graphBody finalEnv := by
        simpa only [List.take_append_drop] using read.append tail
      exact continue_loop state valid body
        (ordered_run logical left right firstFresh leftLayout rightLayout closed ordered finalState
          seenAtLeast seenBound pendingClosed pendingNext)
    | ref address =>
      simp only [edge] at read
      by_cases known : address < seen
      · obtain ⟨finalEnv, tail, finalState⟩ := known_tail (address := address)
          (by simpa only [edge] using edgeState) logical.length leftLayout.injective rightLayout.injective seenBound known
        have body : BlockContinues env graphBody finalEnv := by
          simpa only [List.take_append_drop] using read.append tail
        exact continue_loop state valid body
          (ordered_run logical left right firstFresh leftLayout rightLayout closed ordered finalState
            seenAtLeast seenBound pendingClosed pendingNext)
      · have near := pendingNext pending[cursor] member
        simp only [edge, Edge.Within] at near
        have same : address = seen := by omega
        subst address
        have fresh : seen < logical.length := by
          simpa only [edge, Edge.Within] using pendingClosed pending[cursor] member
        let node := logical[seen]'fresh
        have nodeFound : logical[seen]? = some node := List.getElem?_eq_getElem fresh
        obtain ⟨finalEnv, tail, finalState⟩ := new_tail left right node
          (by simpa only [edge] using edgeState) logical.length leftLayout.injective rightLayout.injective fresh
          (leftLayout.lookup seen node nodeFound) (rightLayout.lookup seen node nodeFound)
        have body : BlockContinues env graphBody finalEnv := by
          simpa only [List.take_append_drop] using read.append tail
        apply continue_loop state valid body
        apply ordered_run logical left right firstFresh leftLayout rightLayout closed ordered finalState (by omega) (by omega)
        · intro queued inside
          rcases List.mem_append.mp inside with old | new
          · exact pendingClosed queued old
          · exact closed node (List.mem_of_getElem? nodeFound) queued new
        · intro queued inside
          rcases List.mem_append.mp inside with old | new
          · exact within_mono (pendingNext queued old) (by omega)
          · simpa only [Nat.add_assoc] using ordered seen node seenAtLeast nodeFound queued new
  · apply BlockReturns.while_loop (flag := false)
    · simp [bind, pure, dataExpr, length, state.cursorValue, state.pendingLeft, encodedEdges, scalarCompare, evalCmpOp, valid]
    · exact BlockReturns.return_value (by simp [dataExpr])
termination_by (logical.length - seen, pending.length - cursor)
decreasing_by
  all_goals simp_wf
  · apply Prod.Lex.right; omega
  · apply Prod.Lex.right; omega
  · apply Prod.Lex.left; omega


/-- The anchored caller objects are visited first. Their internal references
may form arbitrary shared or cyclic graphs, provided they remain in that prefix. -/
theorem visit_prefix (original tail : List Node) (left right : Heap) (extra : List Edge) (cursor : Nat)
    (leftLayout : Layout (original ++ tail) left leftMap) (rightLayout : Layout (original ++ tail) right rightMap)
    (closedOriginal : ∀ node ∈ original, ∀ edge ∈ node.edges, edge.Within original.length)
    (closed : ∀ node ∈ original ++ tail, ∀ edge ∈ node.edges, edge.Within (original ++ tail).length)
    (ordered : ∀ index node, original.length ≤ index → (original ++ tail)[index]? = some node →
      ∀ edge ∈ node.edges, edge.Within (index + 2))
    (state : LoopState env left.encode right.encode ((List.range original.length).map Edge.ref ++ extra)
      leftMap rightMap cursor cursor)
    (extraClosed : ∀ edge ∈ extra, edge.Within (original ++ tail).length)
    (extraNext : ∀ edge ∈ extra, edge.Within (original.length + 1)) (bounded : cursor ≤ original.length) :
    BlockReturns env [graphLoop, .return (.constant (.bool true))] (.scalar (.bool true)) := by
  by_cases valid : cursor < original.length
  · have found : ((List.range original.length).map Edge.ref ++ extra)[cursor]? = some (.ref cursor) := by
      simp [List.getElem?_append, valid]
    obtain ⟨read, edgeState⟩ := read_edge state found
    have nodeFound : (original ++ tail)[cursor]? = some original[cursor] := by
      simp [List.getElem?_append, valid]
    obtain ⟨finalEnv, bodyTail, finalState⟩ := new_tail left right original[cursor] edgeState
      (original ++ tail).length leftLayout.injective rightLayout.injective
      (by simp only [List.length_append]; omega)
      (leftLayout.lookup cursor original[cursor] nodeFound) (rightLayout.lookup cursor original[cursor] nodeFound)
    have body : BlockContinues env graphBody finalEnv := by
      simpa only [List.take_append_drop] using read.append bodyTail
    have rest := visit_prefix original tail left right (extra ++ original[cursor].edges) (cursor + 1)
      leftLayout rightLayout closedOriginal closed ordered (by simpa only [List.append_assoc] using finalState)
      (by
        intro queued inside
        rcases List.mem_append.mp inside with old | new
        · exact extraClosed queued old
        · exact within_mono (closedOriginal original[cursor] (List.getElem_mem valid) queued new)
            (by simp only [List.length_append]; omega))
      (by
        intro queued inside
        rcases List.mem_append.mp inside with old | new
        · exact extraNext queued old
        · exact within_mono (closedOriginal original[cursor] (List.getElem_mem valid) queued new) (by omega)) (by omega)
    exact continue_loop state (by simp only [List.length_append, List.length_map, List.length_range]; omega) body rest
  · have done : cursor = original.length := by omega
    apply ordered_run (original ++ tail) left right original.length leftLayout rightLayout closed ordered state
      (by omega) (by simp only [List.length_append]; omega)
    · intro queued inside
      rcases List.mem_append.mp inside with root | extra
      · obtain ⟨index, indexMember, rfl⟩ := List.mem_map.mp root
        have below := List.mem_range.mp indexMember
        change index < (original ++ tail).length
        simp only [List.length_append]
        omega
      · exact extraClosed queued extra
    · intro queued inside
      rcases List.mem_append.mp inside with root | extra
      · obtain ⟨index, indexMember, rfl⟩ := List.mem_map.mp root
        have below := List.mem_range.mp indexMember
        change index < cursor + 1
        omega
      · simpa only [done] using extraNext queued extra
termination_by original.length - cursor

/-- The actual Python comparator accepts two physical representations of the
same logical graph. Caller roots are retained; only fresh-node discovery order
is restricted, and extra unreachable allocations are unrestricted. -/
theorem equivalent_relocated (original tail : List Node) (left right : Heap) (extra : List Edge)
    (leftLayout : Layout (original ++ tail) left leftMap) (rightLayout : Layout (original ++ tail) right rightMap)
    (closedOriginal : ∀ node ∈ original, ∀ edge ∈ node.edges, edge.Within original.length)
    (closed : ∀ node ∈ original ++ tail, ∀ edge ∈ node.edges, edge.Within (original ++ tail).length)
    (ordered : ∀ index node, original.length ≤ index → (original ++ tail)[index]? = some node →
      ∀ edge ∈ node.edges, edge.Within (index + 2))
    (extraClosed : ∀ edge ∈ extra, edge.Within (original ++ tail).length)
    (extraNext : ∀ edge ∈ extra, edge.Within (original.length + 1))
    (leftRoots : left.roots = ((List.range original.length).map Edge.ref ++ extra).map (relocateEdge leftMap))
    (rightRoots : right.roots = ((List.range original.length).map Edge.ref ++ extra).map (relocateEdge rightMap)) :
    Equivalent left.encode right.encode := by
  let roots := (List.range original.length).map Edge.ref ++ extra
  let env : DataEnv := fun name => [("left", left.encode), ("right", right.encode)].lookup name
  let e1 := env.set "pending_left" (.list (encodedEdges leftMap roots))
  let e2 := e1.set "pending_right" (.list (encodedEdges rightMap roots))
  let e3 := e2.set "seen_left" (.list [])
  let e4 := e3.set "seen_right" (.list [])
  let e5 := e4.set "cursor" (.scalar (.int 0))
  have state : LoopState e5 left.encode right.encode roots leftMap rightMap 0 0 := by
    constructor <;> simp [e5, e4, e3, e2, e1, env, DataEnv.set, List.lookup, addresses]
  have run := visit_prefix original tail left right extra 0 leftLayout rightLayout closedOriginal closed ordered
    state extraClosed extraNext (by omega)
  unfold Equivalent compare dataFunction
  rw [source_body]
  change BlockReturns env _ (.scalar (.bool true))
  apply BlockReturns.branch (flag := false)
  · simp [bind, pure, Functor.map, dataExpr, env, List.lookup, Heap.encode, Data.typeName, Data.equal]
  · apply BlockReturns.branch (flag := false)
    · simp [bind, pure, Functor.map, dataExpr, env, List.lookup, Heap.encode, Data.typeName, Data.equal]
    · apply BlockReturns.assign (value := .list (encodedEdges leftMap roots))
      · simp [bind, pure, dataExpr, item, env, List.lookup, Heap.encode, leftRoots, roots,
          encodedEdges, List.map_map, Function.comp_def]
      · apply BlockReturns.assign (value := .list (encodedEdges rightMap roots))
        · simp [bind, pure, dataExpr, item, env, List.lookup, DataEnv.set, Heap.encode, rightRoots, roots,
            encodedEdges, List.map_map, Function.comp_def]
        · apply BlockReturns.branch (flag := false)
          · simp [bind, pure, dataExpr, length, DataEnv.set, Data.equal_self, encodedEdges]
          · apply BlockReturns.assign (value := .list []) (by simp [pure, Functor.map, dataExpr])
            apply BlockReturns.assign (value := .list []) (by simp [pure, Functor.map, dataExpr])
            apply BlockReturns.assign (value := .scalar (.int 0)) (by simp [dataExpr])
            exact run

end FormalSW.PyAst.Graph.Relocation
