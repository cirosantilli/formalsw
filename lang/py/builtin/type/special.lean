/-! Generic aliases, unions, modules, code objects, and builtin singleton objects. -/

namespace CleanXY.Py.Builtin.Special

structure GenericAlias where
  origin : Nat
  arguments : List Nat
  parameters : List Nat := []
  unpacked : Bool := false
deriving Repr, DecidableEq

structure UnionType where
  members : List Nat
deriving Repr, DecidableEq

def UnionType.normalize (members : List Nat) : UnionType :=
  ⟨members.foldl (fun result member => if result.contains member then result else result ++ [member]) []⟩

def UnionType.containsType (union : UnionType) (typeId : Nat) : Bool := union.members.contains typeId

structure ModuleObject (α : Type u) where
  name : String
  attributes : List (String × α)
deriving Repr

structure CodeObject where
  source : String
  filename : String
  mode : String
  flags : Nat := 0
  optimization : Int := -1
deriving Repr, DecidableEq

/-- Attributes shared by classes, functions, methods, descriptors, and generators. -/
structure DefinitionMetadata where
  name : String
  qualname : String
  moduleName : String
  doc : Option String := none
  typeParameters : List Nat := []
deriving Repr, DecidableEq

structure FunctionObject (Args : Type u) (ResultType : Type v) where
  metadata : DefinitionMetadata
  code : CodeObject
  call : Args → ResultType

/-- Builtin and user-defined functions share call behavior but have distinct runtime types. -/
structure BuiltinFunctionObject (Args : Type u) (ResultType : Type v) where
  metadata : DefinitionMetadata
  call : Args → ResultType

inductive Singleton where
  | none
  | ellipsis
  | notImplemented
deriving Repr, DecidableEq

inductive NoneType where
  | none
deriving Repr, DecidableEq

inductive EllipsisType where
  | ellipsis
deriving Repr, DecidableEq

inductive NotImplementedType where
  | notImplemented
deriving Repr, DecidableEq

end CleanXY.Py.Builtin.Special
