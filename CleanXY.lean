import Lean
import lang.py.CleanXY.Model
import lang.py.CleanXY.Syntax
import lang.py.CleanXY.Parallel
import lang.py.CleanXY.Concurrent
import lang.py.builtin.type.bool
import lang.py.builtin.type.bytearray
import lang.py.builtin.type.bytes
import lang.py.builtin.type.comparison
import lang.py.builtin.type.core
import lang.py.builtin.type.contextmanager
import lang.py.builtin.type.descriptor
import lang.py.builtin.type.dict
import lang.py.builtin.type.dictview
import lang.py.builtin.function
import lang.py.builtin.type.int
import lang.py.builtin.type.iterator
import lang.py.builtin.type.list
import lang.py.builtin.type.memoryview
import lang.py.builtin.type.object
import lang.py.builtin.type.range
import lang.py.builtin.type.sequence
import lang.py.builtin.type.set
import lang.py.builtin.type.slice
import lang.py.builtin.type.subsequence
import lang.py.builtin.type.str
import lang.py.builtin.type.special
import lang.py.builtin.type.super
import lang.py.builtin.type.tuple
import lang.py.builtin.type.type
import lang.py.builtin.type.truth

/-!
CleanXY umbrella module.

Language-specific implementations live below `lang/`; this module re-exports
the installed models so proof files can simply use `import CleanXY`.
-/

namespace CleanXY

end CleanXY
