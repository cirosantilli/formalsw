import lang.py.FormalSW.GraphEquivalence

/-! Proofs about the actual Python snapshot comparator, including unreachable allocations. -/

namespace FormalSW.PyAst

mutual
  theorem Data.equal_self (value : Data) : value.equal value = true := by
    cases value with
    | scalar value => cases value <;> simp [Data.equal, scalarCompare, evalCmpOp]
    | type name => simp [Data.equal]
    | list items => exact dataListEqual_self items
  termination_by sizeOf value

  theorem dataListEqual_self (items : List Data) : dataListEqual items items = true := by
    cases items with
    | nil => rfl
    | cons value rest => simp [dataListEqual, Data.equal_self value, dataListEqual_self rest]
  termination_by sizeOf items
end

namespace Graph
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

private def seenLoop : Stmt :=
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

private def addresses (count : Nat) : List Data :=
  (List.range count).map fun index : Nat => .scalar (.int index)

private theorem eval_compare_int (left : dataExpr env a = some (.ok (.scalar (.int x))))
    (right : dataExpr env b = some (.ok (.scalar (.int y)))) :
    dataExpr env (.compare a [(op, b)]) = some (.ok (.scalar (.bool (evalCmpOp op x y)))) := by
  cases op <;> simp [bind, pure, dataExpr, left, right, Data.equal, scalarCompare, evalCmpOp]

private theorem reference_index (found : env name = some (Edge.ref address).encode) :
    dataExpr env (item name 1) = some (.ok (.scalar (.int address))) := by
  simp [bind, pure, dataExpr, item, found, Edge.encode]

private theorem seen_index {count position : Nat} (found : env name = some (.list (addresses count)))
    (index : env "index" = some (.scalar (.int (position : Nat)))) (valid : position < count) :
    dataExpr env (indexed name "index") = some (.ok (.scalar (.int position))) := by
  apply DataProof.getItem (items := addresses count) (position := position)
    (by simp [dataExpr, found]) (by simp [dataExpr, index]) (by omega)
  simp [addresses, valid]

/-- Searching identical seen tables preserves the identity correspondence, including repeated references. -/
private theorem seen_result (env : DataEnv) (address count position : Nat)
    (left : env "a" = some (Edge.ref address).encode) (right : env "b" = some (Edge.ref address).encode)
    (seenLeft : env "seen_left" = some (.list (addresses count)))
    (seenRight : env "seen_right" = some (.list (addresses count)))
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
        · simpa [evalCmpOp, equal] using eval_compare_int (op := .eq) (reference_index left) (seen_index seenLeft index valid)
        · apply BlockContinues.append (body := [.ifThen (.compare (item "b" 1)
            [(.notEq, indexed "seen_right" "index")]) falseReturn []])
          · exact BlockContinues.branch
              (by simpa [evalCmpOp, equal] using eval_compare_int (op := .notEq) (reference_index right) (seen_index seenRight index valid))
              BlockContinues.nil
          · simpa only [flagEnv, if_pos equal] using
              (BlockContinues.assign (env := env) (name := "found") (show dataExpr env (.constant (.bool true)) = some (.ok (.scalar (.bool true))) from by simp [dataExpr]))
      · apply BlockContinues.branch (flag := false)
        · simpa [evalCmpOp, equal] using eval_compare_int (op := .eq) (reference_index left) (seen_index seenLeft index valid)
        · simpa only [flagEnv, if_neg equal] using BlockContinues.branch (flag := false)
            (by simpa [evalCmpOp, equal] using eval_compare_int (op := .eq) (reference_index right) (seen_index seenRight index valid))
            BlockContinues.nil
    have kept : ∀ name, name ≠ "found" → flagEnv name = env name := by
      intro name different
      by_cases equal : address = position <;> simp [flagEnv, equal, DataEnv.set, different]
    have nextFound : flagEnv "found" = some (.scalar (.bool (decide (address < position + 1)))) := by
      by_cases equal : address = position
      · simp [flagEnv, equal, DataEnv.set]
      · have same : (address < position + 1) = (address < position) := propext (by omega)
        simpa [flagEnv, equal, same] using found
    let nextEnv := flagEnv.set "index" (.scalar (.int (position + 1 : Nat)))
    obtain ⟨finalEnv, rest, result, unchanged⟩ := seen_result nextEnv address count (position + 1)
      (by simpa [nextEnv, DataEnv.set, kept] using left) (by simpa [nextEnv, DataEnv.set, kept] using right)
      (by simpa [nextEnv, DataEnv.set, kept] using seenLeft) (by simpa [nextEnv, DataEnv.set, kept] using seenRight)
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

private structure LoopState (env : DataEnv) (left right : Data) (pending : List Edge) (seen cursor : Nat) : Prop where
  leftValue : env "left" = some left
  rightValue : env "right" = some right
  pendingLeft : env "pending_left" = some (.list (pending.map Edge.encode))
  pendingRight : env "pending_right" = some (.list (pending.map Edge.encode))
  seenLeft : env "seen_left" = some (.list (addresses seen))
  seenRight : env "seen_right" = some (.list (addresses seen))
  cursorValue : env "cursor" = some (.scalar (.int cursor))

private structure EdgeState (env : DataEnv) (left right : Data) (pending : List Edge) (seen cursor : Nat) (edge : Edge)
    : Prop extends LoopState env left right pending seen cursor where
  a : env "a" = some edge.encode
  b : env "b" = some edge.encode

private theorem read_edge (state : LoopState env left right pending seen cursor) (found : pending[cursor]? = some edge) :
    let finalEnv := (env.set "a" edge.encode).set "b" edge.encode
    BlockContinues env (graphBody.take 2) finalEnv ∧ EdgeState finalEnv left right pending seen cursor edge := by
  dsimp only
  constructor
  · apply BlockContinues.append (body := [.assign [.name "a"] (indexed "pending_left" "cursor")])
    · apply BlockContinues.assign (value := edge.encode)
      apply DataProof.getItem (items := pending.map Edge.encode) (position := cursor)
        (by simp [dataExpr, state.pendingLeft]) (by simp [dataExpr, state.cursorValue]) (by omega)
      simp [found]
    · apply BlockContinues.assign (value := edge.encode)
      apply DataProof.getItem (items := pending.map Edge.encode) (position := cursor)
        (by simp [dataExpr, DataEnv.set, state.pendingRight]) (by simp [dataExpr, DataEnv.set, state.cursorValue]) (by omega)
      simp [found]
  · constructor
    · constructor <;> simp [DataEnv.set, state.leftValue, state.rightValue, state.pendingLeft,
        state.pendingRight, state.seenLeft, state.seenRight, state.cursorValue]
    · simp [DataEnv.set]
    · simp [DataEnv.set]

private theorem advance (state : LoopState env left right pending seen cursor) :
    let finalEnv := env.set "cursor" (.scalar (.int (cursor + 1 : Nat)))
    BlockContinues env [.assign [.name "cursor"] (.binOp (.name "cursor") .add (.constant (.int 1)))] finalEnv ∧
      LoopState finalEnv left right pending seen (cursor + 1) := by
  dsimp only
  constructor
  · exact BlockContinues.assign (by simp [bind, pure, dataExpr, state.cursorValue, scalarBinary])
  · constructor <;> simp [DataEnv.set, state.leftValue, state.rightValue, state.pendingLeft,
      state.pendingRight, state.seenLeft, state.seenRight]

private theorem search_reference (state : EdgeState env left right pending seen cursor (.ref address)) :
    ∃ finalEnv, BlockContinues env (referenceBody.take 3) finalEnv ∧
      EdgeState finalEnv left right pending seen cursor (.ref address) ∧
      finalEnv "found" = some (.scalar (.bool (decide (address < seen)))) := by
  let initial := (env.set "found" (.scalar (.bool false))).set "index" (.scalar (.int 0))
  obtain ⟨finalEnv, searched, found, preserved⟩ := seen_result initial address seen 0
    (by simp [initial, DataEnv.set, state.a]) (by simp [initial, DataEnv.set, state.b])
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

private theorem tag_equal (state : EdgeState env left right pending seen cursor edge) :
    dataExpr env (.compare (item "a" 0) [(.notEq, item "b" 0)]) = some (.ok (.scalar (.bool false))) := by
  cases edge <;> simp [bind, pure, dataExpr, item, state.a, state.b, Edge.encode, Data.equal_self]

private theorem scalar_tail (state : EdgeState env left right pending seen cursor (.scalar value)) :
    ∃ finalEnv, BlockContinues env (graphBody.drop 2) finalEnv ∧
      LoopState finalEnv left right pending seen (cursor + 1) := by
  obtain ⟨increment, finalState⟩ := advance state.toLoopState
  refine ⟨_, ?_, finalState⟩
  apply BlockContinues.append (body := [.ifThen (.compare (item "a" 0) [(.notEq, item "b" 0)]) falseReturn []])
    (BlockContinues.branch (tag_equal state) BlockContinues.nil)
  apply BlockContinues.append (body := [.ifThen (.compare (item "a" 0) [(.eq, .constant (.string "ref"))])
    referenceBody [.ifThen (.compare (item "a" 1) [(.notEq, item "b" 1)]) falseReturn []]])
  · apply BlockContinues.branch (flag := false)
    · cases value <;> simp [bind, pure, dataExpr, item, state.a, Edge.encode, Data.typeName, Data.equal, scalarCompare]
    · exact BlockContinues.branch (flag := false) (by
        simp [bind, pure, dataExpr, item, state.a, state.b, Edge.encode, Data.equal_self]) BlockContinues.nil
  · exact increment

private theorem known_tail (state : EdgeState env left right pending seen cursor (.ref address)) (known : address < seen) :
    ∃ finalEnv, BlockContinues env (graphBody.drop 2) finalEnv ∧
      LoopState finalEnv left right pending seen (cursor + 1) := by
  obtain ⟨searchEnv, searched, searchState, found⟩ := search_reference state
  obtain ⟨increment, finalState⟩ := advance searchState.toLoopState
  refine ⟨_, ?_, finalState⟩
  apply BlockContinues.append (body := [.ifThen (.compare (item "a" 0) [(.notEq, item "b" 0)]) falseReturn []])
    (BlockContinues.branch (tag_equal state) BlockContinues.nil)
  apply BlockContinues.append (body := [.ifThen (.compare (item "a" 0) [(.eq, .constant (.string "ref"))])
    referenceBody [.ifThen (.compare (item "a" 1) [(.notEq, item "b" 1)]) falseReturn []]])
  · apply BlockContinues.branch (flag := true)
    · simp [bind, pure, dataExpr, item, state.a, Edge.encode, Data.equal, scalarCompare]
    · apply BlockContinues.append searched
      exact BlockContinues.branch (flag := false)
        (by simp [bind, pure, dataExpr, found, known, Data.truth, scalarTruth]) BlockContinues.nil
  · exact increment

private theorem node_read {heap : Heap} {node : Node} (root : env name = some heap.encode)
    (reference : env referenceName = some (Edge.ref address).encode)
    (found : heap.nodes[address]? = some node) :
    dataExpr env (.subscript (item name 1) (item referenceName 1)) = some (.ok node.encode) := by
  apply DataProof.getItem (items := heap.nodes.map Node.encode) (position := address)
    (by simp [bind, pure, dataExpr, item, root, Heap.encode]) (reference_index reference) (by omega)
  simp [found]

private theorem expand_reference (left right : Heap) (node : Node)
    (state : EdgeState env left.encode right.encode pending seen cursor (.ref seen))
    (leftNode : left.nodes[seen]? = some node) (rightNode : right.nodes[seen]? = some node) :
    ∃ finalEnv, BlockContinues env expandBody finalEnv ∧
      LoopState finalEnv left.encode right.encode (pending ++ node.edges) (seen + 1) cursor := by
  let e1 := env.set "seen_left" (.list (addresses (seen + 1)))
  let e2 := e1.set "seen_right" (.list (addresses (seen + 1)))
  let e3 := e2.set "node_left" node.encode
  let e4 := e3.set "node_right" node.encode
  let e5 := e4.set "pending_left" (.list ((pending ++ node.edges).map Edge.encode))
  let e6 := e5.set "pending_right" (.list ((pending ++ node.edges).map Edge.encode))
  have addLeft : BlockContinues env [expandBody[0]'(by decide)] e1 := by
    apply BlockContinues.assign
    simp [bind, pure, Functor.map, dataExpr, item, state.a, state.seenLeft, Edge.encode, addresses, List.range_succ, List.map_append]
  have addRight : BlockContinues e1 [expandBody[1]'(by decide)] e2 := by
    apply BlockContinues.assign
    simp [bind, pure, Functor.map, dataExpr, item, e1, DataEnv.set, state.b, state.seenRight, Edge.encode, addresses, List.range_succ, List.map_append]
  have readLeft : BlockContinues e2 [expandBody[2]'(by decide)] e3 :=
    BlockContinues.assign (node_read (by simp [e2, e1, DataEnv.set, state.leftValue])
      (by simp [e2, e1, DataEnv.set, state.a]) leftNode)
  have readRight : BlockContinues e3 [expandBody[3]'(by decide)] e4 :=
    BlockContinues.assign (node_read (by simp [e3, e2, e1, DataEnv.set, state.rightValue])
      (by simp [e3, e2, e1, DataEnv.set, state.b]) rightNode)
  refine ⟨e6, ?_, ?_⟩
  · apply BlockContinues.append addLeft
    apply BlockContinues.append addRight
    apply BlockContinues.append readLeft
    apply BlockContinues.append readRight
    apply BlockContinues.append (body := [expandBody[4]'(by decide)])
    · apply BlockContinues.branch (flag := false)
      · simp [bind, pure, dataExpr, item, e4, e3, DataEnv.set, Node.encode, Data.equal_self]
      · exact BlockContinues.nil
    · apply BlockContinues.append (body := [expandBody[5]'(by decide)])
      · apply BlockContinues.branch (flag := false)
        · simp [bind, pure, dataExpr, item, e4, e3, DataEnv.set, Node.encode, Data.equal_self]
        · exact BlockContinues.nil
      · apply BlockContinues.append (body := [expandBody[6]'(by decide)])
        · apply BlockContinues.branch (flag := false)
          · simp [bind, pure, dataExpr, item, e4, e3, DataEnv.set, Node.encode, Data.equal_self]
          · exact BlockContinues.nil
        · apply BlockContinues.append (body := [expandBody[7]'(by decide)])
            (middle := e5)
          · apply BlockContinues.assign
            simp [bind, pure, dataExpr, item, e4, e3, e2, e1, DataEnv.set, Node.encode,
              state.pendingLeft, List.map_append]
          · apply BlockContinues.assign
            simp [bind, pure, dataExpr, item, e5, e4, e3, e2, e1, DataEnv.set, Node.encode,
              state.pendingRight, List.map_append]
  · constructor <;> simp [e6, e5, e4, e3, e2, e1, DataEnv.set, state.leftValue, state.rightValue, state.cursorValue]

private theorem new_tail (left right : Heap) (node : Node)
    (state : EdgeState env left.encode right.encode pending seen cursor (.ref seen))
    (leftNode : left.nodes[seen]? = some node) (rightNode : right.nodes[seen]? = some node) :
    ∃ finalEnv, BlockContinues env (graphBody.drop 2) finalEnv ∧
      LoopState finalEnv left.encode right.encode (pending ++ node.edges) (seen + 1) (cursor + 1) := by
  obtain ⟨searchEnv, searched, searchState, found⟩ := search_reference state
  obtain ⟨expandedEnv, expanded, expandedState⟩ := expand_reference left right node searchState leftNode rightNode
  obtain ⟨increment, finalState⟩ := advance expandedState
  refine ⟨_, ?_, finalState⟩
  apply BlockContinues.append (body := [.ifThen (.compare (item "a" 0) [(.notEq, item "b" 0)]) falseReturn []])
    (BlockContinues.branch (tag_equal state) BlockContinues.nil)
  apply BlockContinues.append (body := [.ifThen (.compare (item "a" 0) [(.eq, .constant (.string "ref"))])
    referenceBody [.ifThen (.compare (item "a" 1) [(.notEq, item "b" 1)]) falseReturn []]])
  · apply BlockContinues.branch (flag := true)
    · simp [bind, pure, dataExpr, item, state.a, Edge.encode, Data.equal, scalarCompare]
    · apply BlockContinues.append searched
      exact BlockContinues.branch (flag := true)
        (by simp [bind, pure, dataExpr, found, Data.truth, scalarTruth]) expanded
  · exact increment

/-- References in an observable edge must remain inside the original heap. -/
def Edge.Within (bound : Nat) : Edge → Prop
  | .scalar _ => True
  | .ref address => address < bound

private theorem drain (state : LoopState env left right pending seen cursor)
    (closed : ∀ edge ∈ pending, edge.Within seen) :
    BlockReturns env [graphLoop, .return (.constant (.bool true))] (.scalar (.bool true)) := by
  by_cases valid : cursor < pending.length
  · have found : pending[cursor]? = some pending[cursor] := List.getElem?_eq_getElem valid
    obtain ⟨read, edgeState⟩ := read_edge state found
    obtain ⟨finalEnv, tail, finalState⟩ : ∃ finalEnv,
        BlockContinues ((env.set "a" pending[cursor].encode).set "b" pending[cursor].encode)
          (graphBody.drop 2) finalEnv ∧ LoopState finalEnv left right pending seen (cursor + 1) := by
      have inside := closed pending[cursor] (List.getElem_mem valid)
      cases edge : pending[cursor] with
      | scalar value =>
          apply scalar_tail (value := value)
          simpa only [edge] using edgeState
      | ref address =>
          apply known_tail (address := address)
          · simpa only [edge] using edgeState
          · simpa [edge, Edge.Within] using inside
    have body : BlockContinues env graphBody finalEnv := by
      simpa only [List.take_append_drop] using BlockContinues.append read tail
    apply BlockReturns.while_loop (flag := true)
    · simp [bind, pure, dataExpr, length, state.cursorValue, state.pendingLeft, scalarCompare, evalCmpOp, valid]
    · exact body.returns (drain finalState closed)
  · apply BlockReturns.while_loop (flag := false)
    · simp [bind, pure, dataExpr, length, state.cursorValue, state.pendingLeft, scalarCompare, evalCmpOp, valid]
    · exact BlockReturns.return_value (by simp [dataExpr])
termination_by pending.length - cursor

private theorem prefix_lookup {before after : List Node} {index : Nat} (extension : before <+: after)
    (valid : index < before.length) : after[index]? = some before[index] := by
  obtain ⟨extra, rfl⟩ := extension
  simp [List.getElem?_append, valid]

/-- Visit the original roots first; afterwards every queued reference has already been seen. -/
private theorem visit_prefix (left right : Heap) (original : List Node) (extra : List Edge) (cursor : Nat)
    (state : LoopState env left.encode right.encode ((List.range original.length).map Edge.ref ++ extra) cursor cursor)
    (leftPrefix : original <+: left.nodes) (rightPrefix : original <+: right.nodes)
    (closed : ∀ node ∈ original, ∀ edge ∈ node.edges, edge.Within original.length)
    (extraClosed : ∀ edge ∈ extra, edge.Within original.length) (bounded : cursor ≤ original.length) :
    BlockReturns env [graphLoop, .return (.constant (.bool true))] (.scalar (.bool true)) := by
  by_cases valid : cursor < original.length
  · have found : ((List.range original.length).map Edge.ref ++ extra)[cursor]? = some (.ref cursor) := by
      simp [List.getElem?_append, valid]
    obtain ⟨read, edgeState⟩ := read_edge state found
    obtain ⟨finalEnv, tail, finalState⟩ := new_tail left right original[cursor] edgeState
      (prefix_lookup leftPrefix valid) (prefix_lookup rightPrefix valid)
    have body : BlockContinues env graphBody finalEnv := by
      simpa only [List.take_append_drop] using BlockContinues.append read tail
    have extended : ∀ edge ∈ extra ++ original[cursor].edges, edge.Within original.length := by
      intro edge member
      rcases List.mem_append.mp member with old | new
      · exact extraClosed edge old
      · exact closed original[cursor] (List.getElem_mem valid) edge new
    have rest := visit_prefix left right original (extra ++ original[cursor].edges) (cursor + 1)
      (by simpa only [List.append_assoc] using finalState) leftPrefix rightPrefix closed extended (by omega)
    apply BlockReturns.while_loop (flag := true)
    · simp [bind, pure, dataExpr, length, state.cursorValue, state.pendingLeft, scalarCompare, evalCmpOp]
      omega
    · exact body.returns rest
  · have done : cursor = original.length := by omega
    apply drain state
    · intro edge member
      rcases List.mem_append.mp member with root | extra
      · obtain ⟨index, indexMember, rfl⟩ := List.mem_map.mp root
        simpa [Edge.Within, done] using List.mem_range.mp indexMember
      · simpa only [done] using extraClosed edge extra
termination_by original.length - cursor

/-- Extra unreachable nodes do not affect the actual Python comparator. All original
objects remain roots, so the theorem also covers shared references and cycles. -/
theorem equivalent_allocations (original leftExtra rightExtra : List Node) (extraRoots : List Edge)
    (closed : ∀ node ∈ original, ∀ edge ∈ node.edges, edge.Within original.length)
    (rootsClosed : ∀ edge ∈ extraRoots, edge.Within original.length) :
    Equivalent
      (Heap.mk ((List.range original.length).map Edge.ref ++ extraRoots) (original ++ leftExtra)).encode
      (Heap.mk ((List.range original.length).map Edge.ref ++ extraRoots) (original ++ rightExtra)).encode := by
  let roots := (List.range original.length).map Edge.ref ++ extraRoots
  let left : Heap := ⟨roots, original ++ leftExtra⟩
  let right : Heap := ⟨roots, original ++ rightExtra⟩
  let env : DataEnv := fun name => [("left", left.encode), ("right", right.encode)].lookup name
  let e1 := env.set "pending_left" (.list (roots.map Edge.encode))
  let e2 := e1.set "pending_right" (.list (roots.map Edge.encode))
  let e3 := e2.set "seen_left" (.list [])
  let e4 := e3.set "seen_right" (.list [])
  let e5 := e4.set "cursor" (.scalar (.int 0))
  have state : LoopState e5 left.encode right.encode roots 0 0 := by
    constructor <;> simp [e5, e4, e3, e2, e1, env, DataEnv.set, List.lookup, addresses]
  have run := visit_prefix left right original extraRoots 0 state
    (List.prefix_append _ _) (List.prefix_append _ _) closed rootsClosed (by omega)
  unfold Equivalent compare dataFunction
  rw [source_body]
  change BlockReturns env _ (.scalar (.bool true))
  apply BlockReturns.branch (flag := false)
  · simp [bind, pure, Functor.map, dataExpr, env, List.lookup, left, right, Heap.encode, Data.typeName, Data.equal]
  · apply BlockReturns.branch (flag := false)
    · simp [bind, pure, Functor.map, dataExpr, env, List.lookup, left, Heap.encode, Data.typeName, Data.equal]
    · apply BlockReturns.assign (value := .list (roots.map Edge.encode))
      · simp [bind, pure, dataExpr, item, env, List.lookup, left, Heap.encode]
      · apply BlockReturns.assign (value := .list (roots.map Edge.encode))
        · simp [bind, pure, dataExpr, item, env, List.lookup, DataEnv.set, right, Heap.encode]
        · apply BlockReturns.branch (flag := false)
          · simp [bind, pure, dataExpr, length, DataEnv.set, Data.equal_self]
          · apply BlockReturns.assign (value := .list []) (by simp [pure, Functor.map, dataExpr])
            apply BlockReturns.assign (value := .list []) (by simp [pure, Functor.map, dataExpr])
            exact BlockReturns.assign (by simp [dataExpr]) run

end Graph
end FormalSW.PyAst
