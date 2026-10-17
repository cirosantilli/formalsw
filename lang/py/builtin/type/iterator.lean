import lang.py.builtin.type.core

/-! Python's iterator and asynchronous-iterator protocols as explicit state machines. -/

namespace FormalSW.Py.Builtin.Iterator

open FormalSW.Py.Builtin

/-- A finite iterator state.  Containers construct one from their current traversal order. -/
structure Iterator (α : Type u) where
  remaining : List α
deriving Repr, DecidableEq

def ofList (values : List α) : Iterator α := ⟨values⟩

/-- `iter(iterator) is iterator`; no state is consumed. -/
def iter (iterator : Iterator α) : Iterator α := iterator

/-- Python `__next__`, returning the updated iterator alongside the item. -/
def next (iterator : Iterator α) : Result (α × Iterator α) :=
  match iterator.remaining with
  | [] => .error .stopIteration
  | value :: rest => .ok (value, ⟨rest⟩)

/-- `next(iterator, default)` suppresses only `StopIteration`. -/
def nextD (iterator : Iterator α) (default : α) : α × Iterator α :=
  match iterator.remaining with
  | [] => (default, iterator)
  | value :: rest => (value, ⟨rest⟩)

/-- Reverse iterator over a snapshot of a reversible container. -/
def reversed (values : List α) : Iterator α := ⟨values.reverse⟩

/-- Async iteration has the same state transition, with a distinct exhaustion exception. -/
structure AsyncIterator (α : Type u) where
  remaining : List α
deriving Repr, DecidableEq

def aiter (iterator : AsyncIterator α) : AsyncIterator α := iterator

def anext (iterator : AsyncIterator α) : Result (α × AsyncIterator α) :=
  match iterator.remaining with
  | [] => .error .stopAsyncIteration
  | value :: rest => .ok (value, ⟨rest⟩)

def anextD (iterator : AsyncIterator α) (default : α) : α × AsyncIterator α :=
  match iterator.remaining with
  | [] => (default, iterator)
  | value :: rest => (value, ⟨rest⟩)

end FormalSW.Py.Builtin.Iterator
