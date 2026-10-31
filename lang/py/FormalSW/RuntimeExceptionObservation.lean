import lang.py.FormalSW.RuntimeEffects

/-! Closed runtime layouts suffice to compare exceptional completions, including aliases and cycles. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

theorem graphNodes_closed_of_closed {heap : Heap} (closed : Closed heap) :
    ∀ node ∈ heap.map graphNode, ∀ edge ∈ node.edges, edge.Within heap.length := by
  intro node member edge edgeMember
  obtain ⟨object, objectMember, rfl⟩ := List.mem_map.mp member
  have inside := closed object objectMember
  cases object with
  | list items | tuple items =>
      obtain ⟨value, present, rfl⟩ := List.mem_map.mp edgeMember
      exact inside value present
  | «instance» origin name fields | dataInstance origin name frozen declared fields =>
      obtain ⟨field, present, rfl⟩ := List.mem_map.mp edgeMember
      exact inside field.2 (List.mem_map_of_mem present)
  | dict entries =>
      obtain ⟨entry, present, edgeMember⟩ := List.mem_flatMap.mp edgeMember
      rcases List.mem_cons.mp edgeMember with rfl | last
      · trivial
      · exact List.mem_singleton.mp last ▸ inside entry.2 (List.mem_map_of_mem present)
  | keyDict entries =>
      obtain ⟨entry, present, edgeMember⟩ := List.mem_flatMap.mp edgeMember
      rcases List.mem_cons.mp edgeMember with rfl | last
      · exact inside entry.2.1 (List.mem_flatMap.mpr ⟨entry, present, by simp⟩)
      · exact List.mem_singleton.mp last ▸ inside entry.2.2 (List.mem_flatMap.mpr ⟨entry, present, by simp⟩)
  | bytearray bytes =>
      obtain ⟨byte, _, rfl⟩ := List.mem_map.mp edgeMember
      trivial
  | set items =>
      obtain ⟨item, _, rfl⟩ := List.mem_map.mp edgeMember
      trivial
  | keySet items =>
      obtain ⟨entry, present, rfl⟩ := List.mem_map.mp edgeMember
      have original : entry ∈ items := by simpa [canonicalKeys] using present
      exact inside entry.2 (List.mem_map_of_mem original)

theorem ExecutionLayout.equivalent_exceptions {logical left right : Heap} {leftMap rightMap : Nat → Nat}
    (leftLayout : ExecutionLayout logical left leftMap) (rightLayout : ExecutionLayout logical right rightMap)
    (anchors : Nat) (bounded : anchors ≤ logical.length)
    (leftFixed : ∀ index < anchors, leftMap index = index)
    (rightFixed : ∀ index < anchors, rightMap index = index) (error : ExceptionObject) :
    Completion.Equivalent ⟨.error error, [], left, anchors⟩ ⟨.error error, [], right, anchors⟩ := by
  refine Or.inr ⟨rfl, rfl, rfl, ?_⟩
  let roots := (List.range anchors).map Graph.Edge.ref
  have rootsFixed (rename : Nat → Nat) (fixed : ∀ index < anchors, rename index = index) :
      roots = roots.map (Graph.Relocation.relocateEdge rename) := by
    simp only [roots, List.map_map]
    apply List.map_congr_left
    intro index member
    simp only [Function.comp_def, Graph.Relocation.relocateEdge, fixed index (List.mem_range.mp member)]
  have equivalent := Graph.Relocation.equivalent_layouts (logical.map graphNode)
    ⟨roots, left.map graphNode⟩ ⟨roots, right.map graphNode⟩ roots
    ⟨leftLayout.runtime.snapshot.injective, leftLayout.runtime.snapshot.lookup⟩
    ⟨rightLayout.runtime.snapshot.injective, rightLayout.runtime.snapshot.lookup⟩
    (by simpa only [List.length_map] using graphNodes_closed_of_closed leftLayout.closed)
    (by
      intro edge member
      obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
      have inside := List.mem_range.mp present
      simpa only [Graph.Edge.Within, List.length_map] using Nat.lt_of_lt_of_le inside bounded)
    (rootsFixed leftMap leftFixed) (rootsFixed rightMap rightFixed)
  simpa only [Completion.snapshot, List.map_nil, List.append_nil, roots, graphNode] using equivalent

end FormalSW.PyAst.Mutable.Relocation
