import lang.py.builtin.type.core

/-! Rich comparison delegation, identity, and membership protocols. -/

namespace FormalSW.Py.Builtin.Comparison

open FormalSW.Py.Builtin

inductive Operator where
  | eq | ne | lt | le | gt | ge
deriving Repr, DecidableEq

structure Model (α : Type u) where
  compare : Operator → α → α → Result Bool

inductive RichResult where
  | value (result : Bool)
  | notImplemented
deriving Repr, DecidableEq

/-- Left and reflected comparison hooks, preserving Python's `NotImplemented` fallback. -/
structure RichModel (α : Type u) where
  identity : α → Nat
  direct : Operator → α → α → Result RichResult
  reflected : Operator → α → α → Result RichResult

private def reflectedOperator : Operator → Operator
  | .eq => .eq | .ne => .ne | .lt => .gt | .le => .ge | .gt => .lt | .ge => .le

def richCompare (model : RichModel α) (operator : Operator) (left right : α) : Result Bool := do
  match ← model.direct operator left right with
  | .value result => return result
  | .notImplemented =>
      match ← model.reflected (reflectedOperator operator) right left with
      | .value result => return result
      | .notImplemented =>
          match operator with
          | .eq => return model.identity left = model.identity right
          | .ne => return model.identity left != model.identity right
          | _ => throw (.typeError "ordering comparison is not supported between instances")

def eq (model : Model α) (left right : α) : Result Bool := model.compare .eq left right
def ne (model : Model α) (left right : α) : Result Bool := model.compare .ne left right
def lt (model : Model α) (left right : α) : Result Bool := model.compare .lt left right
def le (model : Model α) (left right : α) : Result Bool := model.compare .le left right
def gt (model : Model α) (left right : α) : Result Bool := model.compare .gt left right
def ge (model : Model α) (left right : α) : Result Bool := model.compare .ge left right

def is (identity : α → Nat) (left right : α) : Bool := identity left = identity right
def isNot (identity : α → Nat) (left right : α) : Bool := !is identity left right

structure Container (ContainerType : Type u) (Element : Type v) where
  contains : ContainerType → Element → Result Bool

def mem (model : Container ContainerType Element) (element : Element)
    (container : ContainerType) : Result Bool := model.contains container element
def notMem (model : Container ContainerType Element) (element : Element)
    (container : ContainerType) : Result Bool := (!·) <$> model.contains container element

end FormalSW.Py.Builtin.Comparison
