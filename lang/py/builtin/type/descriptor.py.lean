import «.formalsw».lang.py.builtin.type.«descriptor.py.ast»
import lang.py.builtin.type.descriptor

namespace lang.py.builtin.type.descriptor

open FormalSW.PyAst

theorem modeled :
    DescriptorAst.module.hasExactlyClassMethods "property"
      ["__init__", "__get__", "__set__", "__delete__"] = true ∧
    DescriptorAst.module.hasExactlyClassMethods "classmethod" ["__init__", "__get__"] = true ∧
    DescriptorAst.module.hasExactlyClassMethods "staticmethod" ["__init__", "__get__"] = true := by
  decide

theorem source_fingerprint : DescriptorAst.module.fingerprint = 531026127595171168 := by
  native_decide

end lang.py.builtin.type.descriptor
