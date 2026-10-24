import lang.py.FormalSW.Strings

/-! Python string replacement scans Unicode code points, consuming each matched
substring completely before considering the next match. -/

namespace FormalSW.PyAst.Strings

/-- Empty patterns match at the start and after each original character.
Inserted characters are never searched again. -/
def replaceEmpty (replacement : List Char) : Nat → List Char → List Char
  | 0, text => text
  | _ + 1, [] => replacement
  | remaining + 1, character :: rest =>
      replacement ++ character :: replaceEmpty replacement remaining rest

/-- A nonempty match consumes at least one original character. The scan budget
is the original length, so it never restricts the number of possible matches. -/
def replaceScan (pattern replacement : List Char) : Nat → Nat → List Char → List Char
  | _, 0, text => text
  | 0, _, text => text
  | _ + 1, _ + 1, [] => []
  | fuel + 1, remaining + 1, character :: rest =>
      if pattern.isPrefixOf (character :: rest) then
        replacement ++ replaceScan pattern replacement fuel remaining
          ((character :: rest).drop pattern.length)
      else character :: replaceScan pattern replacement fuel (remaining + 1) rest

/-- Negative counts mean all occurrences. At most length + 1 replacements can
occur, including the empty-pattern case. Like the sequence index model, counts
are unbounded integers; CPython platform conversion overflow is excluded. -/
def replace (text old new : String) (count : Int := -1) : String :=
  let characters := text.toList
  let remaining := if count < 0 then characters.length + 1 else count.toNat
  String.ofList (if old.toList.isEmpty then replaceEmpty new.toList remaining characters
    else replaceScan old.toList new.toList characters.length remaining characters)

private def replaceTypeError : ExceptionObject := { typeName := "TypeError", args := [] }

/-- The bound receiver has already been validated, and all arguments evaluated.
Bool counts use Python's integer convention. -/
def replaceCall (text : String) : List Constant → Except ExceptionObject Constant
  | [.string old, .string new] => .ok (.string (replace text old new))
  | [.string old, .string new, count] =>
      match scalarNumber count with
      | some count => .ok (.string (replace text old new count))
      | none => .error replaceTypeError
  | _ => .error replaceTypeError

@[simp] theorem replace_zero (text old new : String) : replace text old new 0 = text := by
  simp [replace, replaceEmpty, replaceScan]

@[simp] theorem replaceCall_count (text old new : String) (count : Int) :
    replaceCall text [.string old, .string new, .int count] =
      .ok (.string (replace text old new count)) := rfl

end FormalSW.PyAst.Strings
