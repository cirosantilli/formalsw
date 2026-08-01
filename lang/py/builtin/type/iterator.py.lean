import «.cleanxy».lang.py.builtin.type.«iterator.py.ast»
import lang.py.builtin.type.iterator

namespace lang.py.builtin.type.iterator

open CleanXY.PyAst

theorem modeled :
    IteratorAst.module.hasExactlyClassMethods "iterator" ["__init__", "__iter__", "__next__"] = true ∧
    IteratorAst.module.hasExactlyClassMethods "async_iterator" ["__init__", "__aiter__", "__anext__"] = true := by
  decide

theorem source_fingerprint : IteratorAst.module.fingerprint = 5805620590057890466 := by
  native_decide

theorem next_equivalent (value : α) (rest : List α) :
    CleanXY.Py.Builtin.Iterator.next ⟨value :: rest⟩ = .ok (value, ⟨rest⟩) := by
  rfl

end lang.py.builtin.type.iterator
