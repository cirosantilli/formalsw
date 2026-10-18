import lang.py.FormalSW.Calls
import Init.Data.Nat.ToString
import Init.Data.Char.Lemmas

/-! Decimal parsing agrees with positional character evaluation, without a digit bound. -/
namespace FormalSW.Py.Builtin.Int

private theorem bounds {character : Char} (digit : character.isDigit) :
    48 ≤ character.toNat ∧ character.toNat ≤ 57 := by
  simpa using Char.isDigit_iff_toNat.mp digit

private theorem normalize_digit {character : Char} (digit : character.isDigit) :
    Unicode.integerCharacter character = character.toNat := by
  have := bounds digit
  simp [Unicode.integerCharacter, show character.toNat < 128 by omega]

private theorem trimLeft_digits (characters : List Char)
    (digits : ∀ c ∈ characters, c.isDigit) :
    trimLeft (characters.map Char.toNat) = characters.map Char.toNat := by
  cases characters with
  | nil => rfl
  | cons c rest =>
      have limits := bounds (digits c (by simp))
      simp [trimLeft, isAsciiSpace, show c.toNat ≠ 9 by omega, show c.toNat ≠ 10 by omega,
        show c.toNat ≠ 11 by omega, show c.toNat ≠ 12 by omega,
        show c.toNat ≠ 13 by omega, show c.toNat ≠ 32 by omega]

private theorem trim_digits (characters : List Char)
    (digits : ∀ c ∈ characters, c.isDigit) :
    trim (characters.map Char.toNat) = characters.map Char.toNat := by
  unfold trim
  rw [← List.map_reverse, trimLeft_digits characters.reverse (by simpa),
    ← List.map_reverse, List.reverse_reverse, trimLeft_digits characters digits]

/-- A nonempty decimal character list parses by ordinary positional accumulation. -/
theorem parseDigits_characters (characters : List Char) (total : Nat) (needDigit : Bool)
    (digits : ∀ c ∈ characters, c.isDigit) (nonempty : characters ≠ [] ∨ needDigit = false) :
    parseDigits 10 (characters.map Char.toNat) total needDigit =
      .ok (Nat.ofDigitChars 10 characters total) := by
  induction characters generalizing total needDigit with
  | nil => simp_all [parseDigits]
  | cons c rest ih =>
      have limits := bounds (digits c (by simp))
      have tailDigits : ∀ c ∈ rest, c.isDigit := by intro d member; exact digits d (by simp [member])
      simp only [List.map_cons, parseDigits, show c.toNat ≠ 95 by omega, ↓reduceIte,
        digitValue, show (48 ≤ c.toNat && c.toNat ≤ 57) = true by simp [limits],
        show c.toNat - 48 < 10 by omega]
      simpa [Nat.ofDigitChars_cons, Nat.mul_comm] using ih (total * 10 + (c.toNat - 48)) false tailDigits (.inr rfl)

/-- This rule accepts any nonempty list of ASCII decimal digits, including leading zeroes. -/
theorem parseText_digits (characters : List Char) (nonempty : characters ≠ [])
    (digits : ∀ c ∈ characters, c.isDigit) :
    parseText (String.ofList characters) = .ok (Nat.ofDigitChars 10 characters 0 : Int) := by
  have normalized : characters.map Unicode.integerCharacter = characters.map Char.toNat := by
    apply List.map_congr_left
    intro c member
    exact normalize_digit (digits c member)
  unfold parseText parseDecimal
  rw [String.toList_ofList, normalized, trim_digits characters digits]
  have unsigned : sign (characters.map Char.toNat) = (false, characters.map Char.toNat) := by
    cases characters with
    | nil => contradiction
    | cons c rest =>
        have limits := bounds (digits c (by simp))
        simp [sign, show c.toNat ≠ 43 by omega, show c.toNat ≠ 45 by omega]
  simp only [unsigned]
  rw [parseDigits_characters characters 0 true digits (.inl nonempty)]
  rfl

private theorem trim_noSpace (source : List Nat)
    (ordinary : ∀ point ∈ source, isAsciiSpace point = false) : trim source = source := by
  have left (items : List Nat) (h : ∀ point ∈ items, isAsciiSpace point = false) :
      trimLeft items = items := by
    cases items with
    | nil => rfl
    | cons head tail => simp [trimLeft, h head (by simp)]
  unfold trim
  rw [left source.reverse (by simpa), List.reverse_reverse, left source ordinary]

/-- A minus sign negates the same positional value, including negative zero. -/
theorem parseText_negative_digits (characters : List Char) (nonempty : characters ≠ [])
    (digits : ∀ c ∈ characters, c.isDigit) :
    parseText ("-" ++ String.ofList characters) = .ok (-(Nat.ofDigitChars 10 characters 0 : Int)) := by
  have normalized : characters.map Unicode.integerCharacter = characters.map Char.toNat := by
    apply List.map_congr_left
    intro c member
    exact normalize_digit (digits c member)
  simp only [parseText, String.toList_append, String.toList_ofList, List.map_append]
  change parseDecimal (45 :: characters.map Unicode.integerCharacter) = _
  rw [normalized]
  unfold parseDecimal
  rw [trim_noSpace _ (by
    intro point member
    simp only [List.mem_cons, List.mem_map] at member
    rcases member with rfl | ⟨c, member, rfl⟩
    · rfl
    · have limits := bounds (digits c member)
      simp [isAsciiSpace]
      omega)]
  simp only [sign]
  rw [parseDigits_characters characters 0 true digits (.inl nonempty)]
  rfl

/-- Decimal printing and parsing round-trip every natural number. -/
theorem parseText_nat (n : Nat) : parseText (toString n) = .ok (n : Int) := by
  rw [Nat.toString_eq_ofList_toDigits]
  rw [parseText_digits _ Nat.toDigits_ne_nil (by
    intro c member
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) member)]
  simp

/-- Python's decimal text conversion round-trips every signed integer. -/
theorem parseText_int (n : _root_.Int) : parseText (toString n) = .ok n := by
  cases n with
  | ofNat n => exact parseText_nat n
  | negSucc n =>
      change parseText ("-" ++ toString (n + 1)) = .ok (_root_.Int.negSucc n)
      rw [Nat.toString_eq_ofList_toDigits]
      rw [parseText_negative_digits _ Nat.toDigits_ne_nil (by
        intro c member
        exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) member)]
      rw [Nat.ofDigitChars_ten_toDigits]
      rfl

end FormalSW.Py.Builtin.Int

namespace FormalSW.PyAst.Calls

theorem integerConversion_nat (n : Nat) :
    integerConversion [.string (toString n)] = some (.ok (.int n)) := by
  rw [integerConversion, Py.Builtin.Int.parseText_nat]
  rfl

theorem integerConversion_int (n : Int) :
    integerConversion [.string (toString n)] = some (.ok (.int n)) := by
  rw [integerConversion, Py.Builtin.Int.parseText_int]
  rfl

end FormalSW.PyAst.Calls
