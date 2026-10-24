import lang.py.builtin.type.core

/-! Generic contiguous-subsequence algorithms shared by `str`, `bytes`, and `bytearray`. -/

namespace FormalSW.Py.Builtin.Subsequence

open FormalSW.Py.Builtin

def startsWith [BEq α] (values prefixValue : List α) : Bool :=
  values.take prefixValue.length == prefixValue

def endsWith [BEq α] (values suffix : List α) : Bool :=
  suffix.length ≤ values.length && values.drop (values.length - suffix.length) == suffix

private def findFromFuel [BEq α] (needle : List α) : Nat → Nat → List α → Option Nat
  | 0, _, _ => none
  | fuel + 1, position, remaining =>
      if startsWith remaining needle then some position
      else
        match remaining with
        | [] => none
        | _ :: tail => findFromFuel needle fuel (position + 1) tail

/-- First occurrence, with Python's empty-subsequence behavior. -/
def find? [BEq α] (values needle : List α) : Option Nat :=
  findFromFuel needle (values.length + 1) 0 values

private def rfindFuel [BEq α] (values needle : List α) : Nat → Option Nat
  | 0 => if startsWith values needle then some 0 else none
  | position + 1 =>
      if startsWith (values.drop (position + 1)) needle then some (position + 1)
      else rfindFuel values needle position

/-- Last occurrence, with Python's empty-subsequence behavior. -/
def rfind? [BEq α] (values needle : List α) : Option Nat :=
  if needle.length > values.length then none else rfindFuel values needle (values.length - needle.length)

def contains [BEq α] (values needle : List α) : Bool := (find? values needle).isSome

theorem startsWith_eq_isPrefixOf [BEq α] [LawfulBEq α] (values needle : List α) :
    startsWith values needle = needle.isPrefixOf values := by
  apply Bool.eq_iff_iff.mpr
  simp only [startsWith, beq_iff_eq, List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take]
  exact eq_comm

private theorem findFromFuel_isSome [BEq α] [LawfulBEq α]
    (needle values : List α) (position : Nat) :
    (findFromFuel needle (values.length + 1) position values).isSome =
      needle.isInfixOf_internal values := by
  induction values generalizing position with
  | nil =>
      cases hasPrefix : startsWith [] needle <;>
        simp [findFromFuel, List.isInfixOf_internal, ← startsWith_eq_isPrefixOf, hasPrefix]
  | cons head tail ih =>
      rw [List.length_cons, findFromFuel, List.isInfixOf_internal,
        ← startsWith_eq_isPrefixOf]
      cases hasPrefix : startsWith (head :: tail) needle with
      | false => simpa only [Bool.false_eq_true, if_false, Bool.false_or] using ih (position + 1)
      | true => rfl

/-- The existing search algorithm computes contiguous list membership. -/
theorem contains_eq_isInfix [BEq α] [LawfulBEq α] (values needle : List α) :
    contains values needle = needle.isInfixOf_internal values :=
  findFromFuel_isSome needle values 0

private def countFuel [BEq α] (needle : List α) : Nat → List α → Nat
  | 0, _ => 0
  | fuel + 1, remaining =>
      if startsWith remaining needle then
        1 + countFuel needle fuel (remaining.drop needle.length)
      else
        match remaining with
        | [] => 0
        | _ :: tail => countFuel needle fuel tail

/-- Non-overlapping occurrence count. -/
def count [BEq α] (values needle : List α) : Nat :=
  if needle.isEmpty then values.length + 1
  else countFuel needle (values.length + 1) values

private def replaceFuel [BEq α] (old replacement : List α) : Nat → List α → List α
  | 0, remaining => remaining
  | fuel + 1, remaining =>
      if startsWith remaining old then
        replacement ++ replaceFuel old replacement fuel (remaining.drop old.length)
      else
        match remaining with
        | [] => []
        | head :: tail => head :: replaceFuel old replacement (fuel + 1) tail

private def replaceEmptyFuel (replacement : List α) : Nat → List α → List α
  | 0, remaining => remaining
  | _ + 1, [] => replacement
  | fuel + 1, head :: tail => replacement ++ head :: replaceEmptyFuel replacement fuel tail

/-- Replace at most `count` non-overlapping occurrences; a negative count means unlimited. -/
def replace [BEq α] (values old replacement : List α) (limit : Int := -1) : List α :=
  let fuel := if limit < 0 then values.length + 1 else min limit.toNat (values.length + 1)
  if old.isEmpty then
    replaceEmptyFuel replacement fuel values
  else replaceFuel old replacement fuel values

private def splitFuel [BEq α] (separator : List α) : Nat → List α → List (List α)
  | 0, remaining => [remaining]
  | fuel + 1, remaining =>
      match find? remaining separator with
      | none => [remaining]
      | some position =>
          remaining.take position ::
            splitFuel separator fuel (remaining.drop (position + separator.length))

/-- Split on an explicit nonempty separator. -/
def split [BEq α] (values separator : List α) (maxSplit : Int := -1) : Result (List (List α)) :=
  if separator.isEmpty then .error (.valueError "empty separator")
  else
    let fuel := if maxSplit < 0 then values.length + 1 else maxSplit.toNat
    .ok (splitFuel separator fuel values)

def join (separator : List α) : List (List α) → List α
  | [] => []
  | first :: rest => rest.foldl (fun result value => result ++ separator ++ value) first

def partition [BEq α] (values separator : List α) : Result (List α × List α × List α) :=
  if separator.isEmpty then .error (.valueError "empty separator")
  else
    match find? values separator with
    | none => .ok (values, [], [])
    | some position =>
        .ok (values.take position, separator, values.drop (position + separator.length))

def rpartition [BEq α] (values separator : List α) : Result (List α × List α × List α) :=
  if separator.isEmpty then .error (.valueError "empty separator")
  else
    match rfind? values separator with
    | none => .ok ([], [], values)
    | some position =>
        .ok (values.take position, separator, values.drop (position + separator.length))

def removePrefix [BEq α] (values prefixValue : List α) : List α :=
  if startsWith values prefixValue then values.drop prefixValue.length else values

def removeSuffix [BEq α] (values suffix : List α) : List α :=
  if endsWith values suffix then values.take (values.length - suffix.length) else values

example : find? [1, 2, 1] [2, 1] = some 1 := rfl
example : count [1, 1, 1] [1, 1] = 1 := rfl
example : split [1, 0, 2, 0] [0] = .ok [[1], [2], []] := rfl
example : replace [1, 2] [] [0] 2 = [0, 1, 0, 2] := rfl

end FormalSW.Py.Builtin.Subsequence
