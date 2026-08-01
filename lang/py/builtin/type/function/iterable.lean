import lang.py.builtin.type.iterator
import lang.py.builtin.type.list

/-! Builtins whose semantics are iteration over finite modeled containers. -/

namespace CleanXY.Py.Builtin.Function.Iterable

open CleanXY.Py.Builtin

def all (truth : α → Bool) (values : List α) : Bool := values.all truth
def any (truth : α → Bool) (values : List α) : Bool := values.any truth
def len (values : List α) : Nat := values.length
def iter (values : List α) : Iterator.Iterator α := Iterator.ofList values
def aiter (values : List α) : Iterator.AsyncIterator α := ⟨values⟩
def next (iterator : Iterator.Iterator α) : Result (α × Iterator.Iterator α) :=
  Iterator.next iterator
def nextD (iterator : Iterator.Iterator α) (default : α) : α × Iterator.Iterator α :=
  Iterator.nextD iterator default
def anext (iterator : Iterator.AsyncIterator α) : Result (α × Iterator.AsyncIterator α) :=
  Iterator.anext iterator
def anextD (iterator : Iterator.AsyncIterator α) (default : α) : α × Iterator.AsyncIterator α :=
  Iterator.anextD iterator default
def reversed (values : List α) : Iterator.Iterator α := Iterator.reversed values

def enumerate (values : List α) (start : Int := 0) : Iterator.Iterator (Int × α) :=
  Iterator.ofList (values.mapIdx fun index value => (start + index, value))

def filter (predicate : α → Bool) (values : List α) : Iterator.Iterator α :=
  Iterator.ofList (values.filter predicate)
def map (function : α → β) (values : List α) : Iterator.Iterator β :=
  Iterator.ofList (values.map function)

/-- Two-argument `iter(callable, sentinel)`, bounded by explicit execution fuel. -/
private def iterSentinelFuel [BEq α] (call : State → Result (α × State))
    (sentinel : α) : Nat → State → Result (List α × State)
  | 0, state => .ok ([], state)
  | fuel + 1, state => do
      let (value, nextState) ← call state
      if value == sentinel then return ([], nextState)
      let (rest, finalState) ← iterSentinelFuel call sentinel fuel nextState
      return (value :: rest, finalState)

def iterSentinel [BEq α] (call : State → Result (α × State)) (sentinel : α)
    (fuel : Nat) (state : State) : Result (List α × State) :=
  iterSentinelFuel call sentinel fuel state

private def choose (better : α → α → Bool) : List α → Option α
  | [] => none
  | first :: rest =>
      some (rest.foldl (fun best candidate => if better candidate best then candidate else best) first)

def max? (less : α → α → Bool) (values : List α) : Option α :=
  choose (fun candidate best => less best candidate) values

def min? (less : α → α → Bool) (values : List α) : Option α := choose less values

def max (less : α → α → Bool) (values : List α) : Result α :=
  match max? less values with
  | some value => .ok value
  | none => .error (.valueError "max() iterable argument is empty")

def min (less : α → α → Bool) (values : List α) : Result α :=
  match min? less values with
  | some value => .ok value
  | none => .error (.valueError "min() iterable argument is empty")

def maxD (less : α → α → Bool) (values : List α) (default : α) : α :=
  (max? less values).getD default
def minD (less : α → α → Bool) (values : List α) (default : α) : α :=
  (min? less values).getD default

def maxKey? (key : α → β) (less : β → β → Bool) (values : List α) : Option α :=
  choose (fun candidate best => less (key best) (key candidate)) values
def minKey? (key : α → β) (less : β → β → Bool) (values : List α) : Option α :=
  choose (fun candidate best => less (key candidate) (key best)) values

/-- Stable `sorted`, sharing the list model's strict-less insertion sort. -/
def sorted (less : α → α → Bool) (values : List α) (reverse : Bool := false) : List α :=
  List.sort values less reverse

def sortedKey (key : α → β) (less : β → β → Bool) (values : List α)
    (reverse : Bool := false) : List α :=
  List.sort values (fun left right => less (key left) (key right)) reverse

private def allEmpty : List (List α) → Bool
  | [] => true
  | values :: rest => values.isEmpty && allEmpty rest

private def anyEmpty : List (List α) → Bool
  | [] => false
  | values :: rest => values.isEmpty || anyEmpty rest

private def heads : List (List α) → Option (List α)
  | [] => some []
  | [] :: _ => none
  | (value :: _) :: rest => (value :: ·) <$> heads rest

private def tails : List (List α) → List (List α)
  | [] => []
  | [] :: rest => [] :: tails rest
  | (_ :: tail) :: rest => tail :: tails rest

private def zipFuel : Nat → List (List α) → Bool → Result (List (List α))
  | 0, _, _ => .ok []
  | fuel + 1, iterables, strict =>
      if allEmpty iterables then .ok []
      else if anyEmpty iterables then
        if strict then .error (.valueError "zip() arguments have different lengths") else .ok []
      else do
        let row ← match heads iterables with
          | some row => .ok row
          | none => .error (.runtimeError "invalid zip iterator state")
        return row :: (← zipFuel fuel (tails iterables) strict)

/-- Python `zip`, including the `strict=True` length check. -/
private def zipValues (iterables : List (List α)) (strict : Bool := false) : Result (List (List α)) :=
  let fuel := iterables.foldl (fun largest values => Nat.max largest values.length) 0
  zipFuel fuel iterables strict

def zip (iterables : List (List α)) (strict : Bool := false) :
    Result (Iterator.Iterator (List α)) :=
  Iterator.ofList <$> zipValues iterables strict

/-- Multi-iterable `map`, including Python 3.14's `strict` option. -/
def mapMany (function : List α → β) (iterables : List (List α))
    (strict : Bool := false) : Result (List β) := do
  return (← zipValues iterables strict).map function

example : enumerate [10, 20] 3 = ⟨[(3, 10), (4, 20)]⟩ := rfl
example : zip [[1, 2], [3, 4]] = .ok ⟨[[1, 3], [2, 4]]⟩ := rfl
example : zip [[1], [2, 3]] true = .error (.valueError "zip() arguments have different lengths") := rfl

end CleanXY.Py.Builtin.Function.Iterable
