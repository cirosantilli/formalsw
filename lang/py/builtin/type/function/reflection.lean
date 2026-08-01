import lang.py.builtin.type.descriptor
import lang.py.builtin.type.type

/-! Reflection and object-protocol builtins. -/

namespace CleanXY.Py.Builtin.Function.Reflection

open CleanXY.Py.Builtin

def callable (object : Object.Object α) : Bool := Object.isCallable object
def delattr (object : Object.Object α) (name : String) := Object.delAttr object name
def dir (object : Object.Object α) : List String := Object.dir object
def getattr? (object : Object.Object α) (name : String) : Option α := Object.getAttr? object name
def getattrD (object : Object.Object α) (name : String) (default : α) : α :=
  (Object.getAttr? object name).getD default
def getattr (object : Object.Object α) (name : String) : Result α :=
  match Object.getAttr? object name with
  | some value => .ok value
  | none => .error (.attributeError s!"object has no attribute '{name}'")
def hasattr (object : Object.Object α) (name : String) : Bool := Object.hasAttr object name
def id (object : Object.Object α) : Nat := Object.id object
def setattr (object : Object.Object α) (name : String) (value : α) :=
  Object.setAttr object name value
def vars (object : Object.Object α) := Object.vars object
def hash (model : Object.HashModel α) (object : α) : Int := model.hash object

def isinstance (registry : Type.Registry) (object : Object.Object α) (typeId : Nat) : Bool :=
  Type.isInstance registry object typeId
def isinstanceAny (registry : Type.Registry) (object : Object.Object α)
    (typeIds : List Nat) : Bool := typeIds.any (Type.isInstance registry object)
def issubclass (registry : Type.Registry) (candidate target : Nat) : Bool :=
  Type.isSubclass registry candidate target
def issubclassAny (registry : Type.Registry) (candidate : Nat) (targets : List Nat) : Bool :=
  targets.any (Type.isSubclass registry candidate)
def type? (registry : Type.Registry) (object : Object.Object α) := Type.typeOf? registry object

def classmethod (function : Class → Args → ResultType) :
    Descriptor.ClassMethod Class Args ResultType := ⟨function⟩

def staticmethod (function : Args → ResultType) : Descriptor.StaticMethod Args ResultType :=
  ⟨function⟩

end CleanXY.Py.Builtin.Function.Reflection
