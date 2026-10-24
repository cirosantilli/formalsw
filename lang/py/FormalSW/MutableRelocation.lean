import lang.py.FormalSW.MutableGlobals
import lang.py.FormalSW.GraphRelocation

/-! Compare freshly allocated tuple/list results through the actual snapshot comparator. -/
namespace FormalSW.PyAst.Mutable.Relocation
open Graph.Relocation

def graphNode : Object → Graph.Node := fun object => match object with
    | .instance origin name fields | .dataInstance origin name _ _ fields =>
        ⟨.staticObject origin name, fields.map Prod.fst, fields.map (fun field => field.2.edge)⟩
    | .list items => ⟨.list, [], items.map Value.edge⟩
    | .tuple items => ⟨.tuple, [], items.map Value.edge⟩
    | .dict entries => ⟨.dict, [], entries.flatMap (fun (key, value) => [.scalar key, value.edge])⟩
    | .keyDict entries => ⟨.dict, [], entries.flatMap (fun entry => [entry.2.1.edge, entry.2.2.edge])⟩
    | .set items => ⟨.set, [], (ScalarSet.canonical items).map Graph.Edge.scalar⟩
    | .keySet items => ⟨.set, [], (canonicalKeys items).map (fun entry => entry.2.edge)⟩
    | .bytearray bytes => ⟨.bytearray, [], bytes.map (fun byte => .scalar (.int byte.toNat))⟩

theorem graphNodes_closed {heap : Heap} (valid : heap.Valid) :
    ∀ node ∈ heap.map graphNode, ∀ edge ∈ node.edges, edge.Within heap.length := by
  intro node member edge edgeMember
  obtain ⟨object, objectMember, rfl⟩ := List.mem_map.mp member
  have objectValid := valid object objectMember
  cases object with
  | list items | tuple items =>
      obtain ⟨value, valueMember, rfl⟩ := List.mem_map.mp edgeMember
      have valueValid := objectValid value valueMember
      cases value with
      | scalar _ => trivial
      | ref _ => exact valueValid
  | «instance» origin name fields | dataInstance origin name frozen declared fields =>
      obtain ⟨field, fieldMember, rfl⟩ := List.mem_map.mp edgeMember
      have fieldValid := objectValid.2 field fieldMember
      cases value : field.2 with
      | scalar _ => trivial
      | ref _ => simpa only [value] using fieldValid
  | dict entries =>
      obtain ⟨entry, member, edgeMember⟩ := List.mem_flatMap.mp edgeMember
      rcases List.mem_cons.mp edgeMember with rfl | edgeMember
      · trivial
      · have equal := List.mem_singleton.mp edgeMember
        subst edge
        have fieldValid := objectValid.2 entry member
        cases value : entry.2 with
        | scalar _ => trivial
        | ref _ => simpa only [value] using fieldValid
  | keyDict entries =>
      obtain ⟨entry, member, edgeMember⟩ := List.mem_flatMap.mp edgeMember
      rcases List.mem_cons.mp edgeMember with rfl | edgeMember
      · exact (objectValid.2 entry member).2.1
      · exact List.mem_singleton.mp edgeMember ▸ (objectValid.2 entry member).2.2
  | bytearray bytes =>
      obtain ⟨byte, _, rfl⟩ := List.mem_map.mp edgeMember
      trivial
  | set items =>
      obtain ⟨item, _, rfl⟩ := List.mem_map.mp edgeMember
      trivial
  | keySet items =>
      obtain ⟨entry, member, rfl⟩ := List.mem_map.mp edgeMember
      have original : entry ∈ items := by simpa [canonicalKeys] using member
      have within := (objectValid.2 entry original).2
      cases value : entry.2 with
      | scalar _ => trivial
      | ref _ => simpa only [value] using within

/-- Fix caller objects, then relocate the result tuple and its selected list. -/
def resultMap (anchors tuple selected index : Nat) : Nat :=
  if index < anchors then index else if index = anchors then tuple else selected

private theorem resultMap_injective (anchors tuple selected : Nat)
    (tupleFresh : anchors ≤ tuple) (selectedFresh : anchors ≤ selected) (different : tuple ≠ selected) :
    InjectiveBelow (resultMap anchors tuple selected) (anchors + 2) := by
  intro i hi j hj equal
  by_cases oldI : i < anchors <;> by_cases oldJ : j < anchors <;>
    by_cases sameI : i = anchors <;> by_cases sameJ : j = anchors <;>
    simp_all [resultMap] <;> omega

private theorem edge_fixed {edge : Graph.Edge} {anchors : Nat} (rename : Nat → Nat) (fixed : ∀ index < anchors, rename index = index)
    (inside : edge.Within anchors) : relocateEdge rename edge = edge := by
  cases edge with
  | scalar _ => rfl
  | ref address => simp only [relocateEdge, fixed address inside]

private theorem node_fixed {node : Graph.Node} {anchors : Nat} (rename : Nat → Nat) (fixed : ∀ index < anchors, rename index = index)
    (inside : ∀ edge ∈ node.edges, edge.Within anchors) : relocateNode rename node = node := by
  have edges : node.edges.map (relocateEdge rename) = node.edges := by
    calc
      _ = node.edges.map id := by
        apply List.map_congr_left
        intro edge member
        exact edge_fixed rename fixed (inside edge member)
      _ = _ := List.map_id _
  cases node
  simp_all [relocateNode]

private def tupleNode (total : Constant) (selected : Nat) : Graph.Node :=
  ⟨.tuple, [], [.scalar total, .ref selected]⟩

private def listNode (values : List Constant) : Graph.Node :=
  ⟨.list, [], values.map Graph.Edge.scalar⟩

private theorem result_layout (original physical : List Graph.Node) (roots : List Graph.Edge) (total : Constant) (values : List Constant)
    (tuple selected : Nat) (extension : original <+: physical)
    (closed : ∀ node ∈ original, ∀ edge ∈ node.edges, edge.Within original.length)
    (tupleFresh : original.length ≤ tuple) (selectedFresh : original.length ≤ selected)
    (different : tuple ≠ selected)
    (tupleFound : physical[tuple]? = some (tupleNode total selected))
    (listFound : physical[selected]? = some (listNode values)) :
    Layout (original ++ [tupleNode total (original.length + 1), listNode values])
      ⟨roots, physical⟩ (resultMap original.length tuple selected) := by
  constructor
  · simpa only [List.length_append, List.length_cons, List.length_nil] using
      resultMap_injective original.length tuple selected tupleFresh selectedFresh different
  · intro index node found
    by_cases old : index < original.length
    · have originalFound : original[index]? = some node := by
        simpa [List.getElem?_append, old] using found
      have member := List.mem_of_getElem? originalFound
      rw [node_fixed _ (by intros; simp [resultMap, *]) (closed node member)]
      obtain ⟨extra, rfl⟩ := extension
      simpa [resultMap, old, List.getElem?_append] using originalFound
    · have indexBound : index < original.length + 2 := by
        have := (List.getElem?_eq_some_iff.mp found).1
        simpa only [List.length_append, List.length_cons, List.length_nil] using this
      have cases : index = original.length ∨ index = original.length + 1 := by omega
      rcases cases with rfl | rfl
      · have equal : node = tupleNode total (original.length + 1) := by
          simpa [List.getElem?_append] using found.symm
        subst node
        simpa [resultMap, relocateNode, relocateEdge, tupleNode, show ¬original.length + 1 < original.length from by omega] using tupleFound
      · have equal : node = listNode values := by
          simpa [List.getElem?_append] using found.symm
        subst node
        simpa [resultMap, relocateNode, relocateEdge, listNode, List.map_map, Function.comp_def, show ¬original.length + 1 < original.length from by omega] using listFound

/-- The tuple and selected list may occupy different fresh addresses. The
caller's objects, aliases, cycles, globals, and scalar results remain observable. -/
theorem equivalent_tuple_list (original left right : Heap) (globals : Globals)
    (total : Constant) (values : List Constant) (leftTuple leftList rightTuple rightList : Nat)
    (valid : original.Valid)
    (globalsWithin : ∀ entry ∈ globals, entry.2.edge.Within original.length)
    (leftPrefix : original <+: left) (rightPrefix : original <+: right)
    (leftTupleFresh : original.length ≤ leftTuple) (leftListFresh : original.length ≤ leftList)
    (rightTupleFresh : original.length ≤ rightTuple) (rightListFresh : original.length ≤ rightList)
    (leftDifferent : leftTuple ≠ leftList) (rightDifferent : rightTuple ≠ rightList)
    (leftTupleFound : left[leftTuple]? = some (.tuple [.scalar total, .ref leftList]))
    (rightTupleFound : right[rightTuple]? = some (.tuple [.scalar total, .ref rightList]))
    (leftListFound : left[leftList]? = some (.list (values.map Value.scalar)))
    (rightListFound : right[rightList]? = some (.list (values.map Value.scalar))) :
    Completion.Equivalent ⟨.ok (.ref leftTuple), globals, left, original.length⟩
      ⟨.ok (.ref rightTuple), globals, right, original.length⟩ := by
  refine Or.inr ⟨rfl, rfl, trivial, ?_⟩
  let nodes := original.map graphNode
  let tail := [tupleNode total (nodes.length + 1), listNode values]
  let leftMap := resultMap nodes.length leftTuple leftList
  let rightMap := resultMap nodes.length rightTuple rightList
  let extra := globals.map (fun entry => entry.2.edge) ++ [.ref nodes.length]
  let leftGraph : Graph.Heap := ⟨(List.range original.length).map Graph.Edge.ref ++
    globals.map (fun entry => entry.2.edge) ++ [.ref leftTuple], left.map graphNode⟩
  let rightGraph : Graph.Heap := ⟨(List.range original.length).map Graph.Edge.ref ++
    globals.map (fun entry => entry.2.edge) ++ [.ref rightTuple], right.map graphNode⟩
  have closed : ∀ node ∈ nodes, ∀ edge ∈ node.edges, edge.Within nodes.length := by
    simpa only [nodes, List.length_map] using graphNodes_closed valid
  have leftLayout : Layout (nodes ++ tail) leftGraph leftMap := by
    apply result_layout nodes (left.map graphNode) leftGraph.roots total values leftTuple leftList
    · exact List.IsPrefix.map graphNode leftPrefix
    · exact closed
    · simpa [nodes] using leftTupleFresh
    · simpa [nodes] using leftListFresh
    · exact leftDifferent
    · simpa [graphNode, tupleNode] using congrArg (Option.map graphNode) leftTupleFound
    · simpa [graphNode, listNode, List.map_map, Function.comp_def, Value.edge] using congrArg (Option.map graphNode) leftListFound
  have rightLayout : Layout (nodes ++ tail) rightGraph rightMap := by
    apply result_layout nodes (right.map graphNode) rightGraph.roots total values rightTuple rightList
    · exact List.IsPrefix.map graphNode rightPrefix
    · exact closed
    · simpa [nodes] using rightTupleFresh
    · simpa [nodes] using rightListFresh
    · exact rightDifferent
    · simpa [graphNode, tupleNode] using congrArg (Option.map graphNode) rightTupleFound
    · simpa [graphNode, listNode, List.map_map, Function.comp_def, Value.edge] using congrArg (Option.map graphNode) rightListFound
  have closedAll : ∀ node ∈ nodes ++ tail, ∀ edge ∈ node.edges, edge.Within (nodes ++ tail).length := by
    intro node member edge edgeMember
    rcases List.mem_append.mp member with old | fresh
    · have inside := closed node old edge edgeMember
      cases edge with
      | scalar _ => trivial
      | ref address =>
          change address < (nodes ++ tail).length
          change address < nodes.length at inside
          simp only [tail, List.length_append, List.length_cons, List.length_nil]
          omega
    · simp only [tail, List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl
      · simp only [tupleNode, List.mem_cons, List.not_mem_nil, or_false] at edgeMember
        rcases edgeMember with rfl | rfl
        · trivial
        · simp only [Graph.Edge.Within, tail, List.length_append, List.length_cons, List.length_nil]; omega
      · obtain ⟨value, _, rfl⟩ := List.mem_map.mp edgeMember
        trivial
  have ordered : ∀ index node, nodes.length ≤ index → (nodes ++ tail)[index]? = some node →
      ∀ edge ∈ node.edges, edge.Within (index + 2) := by
    intro index node fresh found edge member
    have inside := closedAll node (List.mem_of_getElem? found) edge member
    cases edge with
    | scalar _ => trivial
    | ref address => change address < index + 2; change address < (nodes ++ tail).length at inside; simp only [tail, List.length_append, List.length_cons, List.length_nil] at inside; omega
  have extraNext : ∀ edge ∈ extra, edge.Within (nodes.length + 1) := by
    intro edge member
    rcases List.mem_append.mp member with global | returned
    · obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp global
      have inside := globalsWithin entry entryMember
      cases value : entry.2 with
      | scalar _ => trivial
      | ref address =>
          have bounded : address < original.length := by simpa only [value, Value.edge, Graph.Edge.Within] using inside
          change address < nodes.length + 1
          simpa only [nodes, List.length_map] using Nat.lt_succ_of_lt bounded
    · have equal := List.mem_singleton.mp returned
      subst edge
      change nodes.length < nodes.length + 1
      omega
  have extraClosed : ∀ edge ∈ extra, edge.Within (nodes ++ tail).length := by
    intro edge member
    have inside := extraNext edge member
    cases edge with
    | scalar _ => trivial
    | ref address => change address < (nodes ++ tail).length; change address < nodes.length + 1 at inside; simp only [tail, List.length_append, List.length_cons, List.length_nil]; omega
  have roots (tuple selected : Nat) :
      ((List.range nodes.length).map Graph.Edge.ref ++ globals.map (fun entry => entry.2.edge) ++ [.ref tuple]) =
        ((List.range nodes.length).map Graph.Edge.ref ++ extra).map (relocateEdge (resultMap nodes.length tuple selected)) := by
    have fixedRoots : ((List.range nodes.length).map Graph.Edge.ref).map
        (relocateEdge (resultMap nodes.length tuple selected)) = (List.range nodes.length).map Graph.Edge.ref := by
      simp only [List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro index member
      simp [relocateEdge, resultMap, List.mem_range.mp member]
    have fixedGlobals : (globals.map (fun entry => entry.2.edge)).map
        (relocateEdge (resultMap nodes.length tuple selected)) = globals.map (fun entry => entry.2.edge) := by
      simp only [List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro entry member
      exact edge_fixed (anchors := nodes.length) _ (by intros; simp [resultMap, *])
        (by simpa only [nodes, List.length_map] using globalsWithin entry member)
    simp only [extra, List.map_append, fixedRoots, fixedGlobals, List.map_cons, List.map_nil]
    simp [relocateEdge, resultMap, List.append_assoc]
  have equivalent := equivalent_relocated nodes tail leftGraph rightGraph extra leftLayout rightLayout closed closedAll ordered extraClosed extraNext
    (by simpa only [leftGraph, leftMap, nodes, List.length_map, List.append_assoc] using roots leftTuple leftList)
    (by simpa only [rightGraph, rightMap, nodes, List.length_map, List.append_assoc] using roots rightTuple rightList)
  exact equivalent

end FormalSW.PyAst.Mutable.Relocation
