import lang.py.builtin.type.dict
import lang.py.builtin.type.set

/-! Dynamic dictionary views and read-only mapping proxies. -/

namespace CleanXY.Py.Builtin.DictView

inductive Kind where
  | keys
  | values
  | items
deriving Repr, DecidableEq

/-- A view identifies its source dictionary and kind; materialization receives current state. -/
structure View where
  dictionaryIdentity : Nat
  kind : Kind
deriving Repr, DecidableEq

inductive Entry (α : Type u) (β : Type v) where
  | key (value : α)
  | value (value : β)
  | item (key : α) (value : β)
deriving Repr

def materialize (view : View) (dictionaryIdentity : Nat)
    (dictionary : Dict.Dict α β cmp) : Option (List (Entry α β)) :=
  if view.dictionaryIdentity != dictionaryIdentity then none
  else
    some <| match view.kind with
      | .keys => (Dict.keys dictionary).map .key
      | .values => (Dict.values dictionary).map .value
      | .items => (Dict.items dictionary).map fun item => .item item.1 item.2

def length (view : View) (dictionaryIdentity : Nat)
    (dictionary : Dict.Dict α β cmp) : Option Nat :=
  (materialize view dictionaryIdentity dictionary).map List.length

def reversed (view : View) (dictionaryIdentity : Nat)
    (dictionary : Dict.Dict α β cmp) : Option (List (Entry α β)) :=
  (materialize view dictionaryIdentity dictionary).map List.reverse

/-- Read-only mapping proxy; state transitions produce a new proxy over the updated dictionary. -/
structure MappingProxy (α : Type u) (β : Type v)
    (cmp : α → α → Ordering := by exact compare) where
  dictionary : Dict.Dict α β cmp

def MappingProxy.get? (proxy : MappingProxy α β cmp) (key : α) : Option β :=
  Dict.get? proxy.dictionary key
def MappingProxy.size (proxy : MappingProxy α β cmp) : Nat := Dict.size proxy.dictionary
def MappingProxy.keys (proxy : MappingProxy α β cmp) : List α := Dict.keys proxy.dictionary

end CleanXY.Py.Builtin.DictView
