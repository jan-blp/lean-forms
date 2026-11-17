module

public import Forms.Model.Scalar

@[expose] public section
namespace Forms.Model
open Lean

inductive TextKind where
  | plain
  | natural
  | integer
  | decimal
  | date
  | uuid
  deriving DecidableEq, Repr

structure Format (α : Type) where
  kind : TextKind
  print : α → String
  parse : String → Except String α
  parse_print : ∀ value, parse (print value) = .ok value

namespace Format

/-- The whitespace accepted by JavaScript's String.trim. -/
def jsWhitespace (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n && n ≤ 0x0D) || n == 0x20 || n == 0xA0 || n == 0x1680 ||
    (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 ||
    n == 0x202F || n == 0x205F || n == 0x3000 || n == 0xFEFF

def trim (chars : List Char) : List Char :=
  ((chars.dropWhile jsWhitespace).reverse.dropWhile jsWhitespace).reverse

theorem dropWhile_of_forall
    {p : Char → Bool}
    {chars : List Char}
    (h : ∀ c ∈ chars, p c = false)
    : chars.dropWhile p = chars := by
  cases chars <;> simp_all [List.dropWhile]

theorem dropWhile_of_all
    {p : Char → Bool}
    {chars : List Char}
    (h : ∀ c ∈ chars, p c = true)
    : chars.dropWhile p = [] := by
  induction chars <;> simp_all [List.dropWhile]

theorem trim_of_forall
    {chars : List Char}
    (h : ∀ c ∈ chars, jsWhitespace c = false)
    : trim chars = chars := by
  unfold trim
  rw [dropWhile_of_forall h, dropWhile_of_forall (by simpa using h), List.reverse_reverse]

def digit (d : Nat) : Char :=
  Char.ofNat (48 + d)

def digitValue (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48) else none

theorem digitValue_digit {d : Nat} (h : d < 10) : digitValue (digit d) = some d := by
  have : ∀ d : Fin 10, digitValue (digit d) = some d := by decide
  exact this ⟨d, h⟩

/-- Decimal digits, most significant first. -/
def digits (n : Nat) : List Char :=
  if n < 10 then [digit n] else digits (n / 10) ++ [digit (n % 10)]
decreasing_by omega

theorem digits_digit {n : Nat} : ∀ c ∈ digits n, ∃ d : Fin 10, c = digit d := by
  rw [digits]
  split
  · intro c h
    exact ⟨⟨n, by omega⟩, by simpa using h⟩
  · intro c h
    rcases List.mem_append.1 h with h | h
    · exact digits_digit c h
    · exact ⟨⟨n % 10, Nat.mod_lt _ (by decide)⟩, by simpa using h⟩
decreasing_by omega

theorem digits_ne_nil (n : Nat) : digits n ≠ [] := by
  rw [digits]
  split <;> simp

/-- The value of digits read least significant first. -/
def valueReversed : List Char → Option Nat
  | [] => some 0
  | c :: rest =>
    match digitValue c, valueReversed rest with
    | some d, some r => some (r * 10 + d)
    | _, _ => none

/-- The value of digits, most significant first; `none` unless there is at least one. -/
def value (chars : List Char) : Option Nat :=
  if chars.isEmpty then none else valueReversed chars.reverse

theorem valueReversed_digits (n : Nat) : valueReversed (digits n).reverse = some n := by
  rw [digits]
  split
  · simp [valueReversed, digitValue_digit (show n < 10 by omega)]
  · simp [valueReversed, digitValue_digit (Nat.mod_lt n (show 10 > 0 by decide)),
      valueReversed_digits (n / 10)]
    omega
decreasing_by omega

/-- `width` characters at least, padded with leading zeros. -/
def pad (width : Nat) (chars : List Char) : List Char :=
  List.replicate (width - chars.length) (digit 0) ++ chars

theorem length_pad (width : Nat) (chars : List Char) : width ≤ (pad width chars).length := by
  simp [pad]
  omega

theorem valueReversed_append_zeros (chars : List Char) (count : Nat) :
    valueReversed (chars ++ List.replicate count (digit 0)) = valueReversed chars := by
  induction chars with
  | nil =>
    simp only [List.nil_append]
    induction count <;>
      simp_all [List.replicate_succ, valueReversed, digitValue_digit (by decide : 0 < 10)]
  | cons c rest ih => simp [valueReversed, ih]

/-- Neither whitespace nor a sign or a decimal point. -/
abbrev Numeral (c : Char) : Prop :=
  jsWhitespace c = false ∧ c ≠ '-' ∧ c ≠ '.'

/-- Characters that are all digits, with value `n`. -/
structure Digits (chars : List Char) (n : Nat) : Prop where
  value_eq : value chars = some n
  numeral : ∀ c ∈ chars, Numeral c

theorem digits_valid (n : Nat) (width : Nat) : Digits (pad width (digits n)) n := by
  refine ⟨?_, fun c h => ?_⟩
  · simp [value, pad, digits_ne_nil, List.reverse_append, List.reverse_replicate,
      valueReversed_append_zeros, valueReversed_digits]
  · have : ∀ d : Fin 10, Numeral (digit d) := by decide
    rcases List.mem_append.1 h with h | h
    · exact List.eq_of_mem_replicate h ▸ this 0
    · obtain ⟨d, rfl⟩ := digits_digit c h
      exact this d

theorem Digits.no_whitespace {chars : List Char} {n : Nat} (h : Digits chars n) :
    ∀ c ∈ chars, jsWhitespace c = false :=
  fun c hc => (h.numeral c hc).1

def plain : Format String where
  kind := .plain
  print := id
  parse := .ok
  parse_print _ := rfl

def natural : Format Nat where
  kind := .natural
  print n := String.ofList (digits n)
  parse text := match value (trim text.toList) with
    | some n => .ok n
    | none => .error "Enter a non-negative whole number."
  parse_print n := by
    have h : Digits (digits n) n := by simpa [pad] using digits_valid n 0
    simp [String.toList_ofList, trim_of_forall h.no_whitespace, h.value_eq]

def sign : List Char → Bool × List Char
  | c :: rest => if c = '-' then (true, rest) else (false, c :: rest)
  | [] => (false, [])

def signed (value : Int) (chars : List Char) : List Char :=
  if value < 0 then '-' :: chars else chars

def unsign (negative : Bool) (n : Nat) : Int :=
  if negative then -n else n

theorem sign_signed {chars : List Char} (value : Int) (h : ∀ c ∈ chars, c ≠ '-') :
    sign (signed value chars) = (decide (value < 0), chars) := by
  unfold signed
  split <;> cases chars <;> simp_all [sign]

theorem unsign_natAbs (value : Int) : unsign (decide (value < 0)) value.natAbs = value := by
  unfold unsign
  split <;> simp_all <;> omega

theorem signed_no_whitespace
    {chars : List Char}
    (value : Int)
    (h : ∀ c ∈ chars, jsWhitespace c = false)
    : ∀ c ∈ signed value chars, jsWhitespace c = false := by
  unfold signed
  split <;> simp_all [jsWhitespace]

def integer : Format Int where
  kind := .integer
  print n := String.ofList (signed n (digits n.natAbs))
  parse text :=
    let (negative, chars) := sign (trim text.toList)
    match value chars with
    | some n => .ok (unsign negative n)
    | none => .error "Enter a whole number."
  parse_print n := by
    have h : Digits (digits n.natAbs) n.natAbs := by
      simpa [pad] using digits_valid n.natAbs 0
    simp [String.toList_ofList, trim_of_forall (signed_no_whitespace n h.no_whitespace),
      sign_signed n fun c hc => (h.numeral c hc).2.1, h.value_eq, unsign_natAbs]

def refine
    {α β : Type}
    (format : Format α)
    (print : β → α)
    (parse : α → Option β)
    (parse_print : ∀ value, parse (print value) = some value)
    (message : String)
    : Format β where
  kind := format.kind
  print value := format.print (print value)
  parse text := match format.parse text with
    | .ok value => match parse value with
      | some value => .ok value
      | none => .error message
    | .error error => .error error
  parse_print value := by simp [format.parse_print, parse_print]

def int32 : Format Int32 :=
  integer.refine Int32.toInt Int32.ofInt? Int32.ofInt?_toInt
    "Enter a whole number between -2147483648 and 2147483647."

def int64 : Format Int64 :=
  integer.refine Int64.toInt Int64.ofInt? Int64.ofInt?_toInt
    "Enter a whole number between -9223372036854775808 and 9223372036854775807."

/-- The digits before and after an optional decimal point. -/
def point (chars : List Char) : Option (List Char × List Char) :=
  match chars.dropWhile (· != '.') with
  | [] => some (chars, [])
  | _ :: fraction =>
    if fraction.contains '.' then none else some (chars.takeWhile (· != '.'), fraction)

def unpoint (whole fraction : List Char) : List Char :=
  if fraction = [] then whole else whole ++ '.' :: fraction

theorem point_unpoint
    {whole fraction : List Char}
    (hw : ∀ c ∈ whole, Numeral c)
    (hf : ∀ c ∈ fraction, Numeral c)
    : point (unpoint whole fraction) = some (whole, fraction) := by
  have hw : ∀ c ∈ whole, (c != '.') = true := fun c hc => by simpa using (hw c hc).2.2
  have : '.' ∉ fraction := fun hm => (hf '.' hm).2.2 rfl
  unfold unpoint
  split
  · simp_all [point, dropWhile_of_all hw]
  · simp [point, List.dropWhile_append_of_pos hw, List.takeWhile_append_of_pos hw, this]

theorem unpoint_no_sign
    {whole fraction : List Char}
    (hw : ∀ c ∈ whole, Numeral c)
    (hf : ∀ c ∈ fraction, Numeral c)
    : ∀ c ∈ unpoint whole fraction, jsWhitespace c = false ∧ c ≠ '-' := by
  unfold unpoint
  split <;> simp_all [or_imp, forall_and, show jsWhitespace '.' = false by decide]

def Decimal.chars (value : Decimal) : List Char :=
  let padded := pad (value.exponent + 1) (digits value.mantissa.natAbs)
  let whole := padded.length - value.exponent
  signed value.mantissa (unpoint (padded.take whole) (padded.drop whole))

def decimal : Format Decimal where
  kind := .decimal
  print value := String.ofList (Decimal.chars value)
  parse text :=
    let (negative, chars) := sign (trim text.toList)
    match point chars with
    | some (whole, fraction) => match value (whole ++ fraction) with
      | some n => .ok (Decimal.normalize (unsign negative n) fraction.length)
      | none => .error "Enter a decimal number, such as 12.50."
    | none => .error "Enter a decimal number, such as 12.50."
  parse_print value := by
    have h := digits_valid value.mantissa.natAbs (value.exponent + 1)
    have length := length_pad (value.exponent + 1) (digits value.mantissa.natAbs)
    dsimp only [Decimal.chars]
    generalize pad (value.exponent + 1) (digits value.mantissa.natAbs) = padded at h length ⊢
    generalize hwhole : padded.length - value.exponent = whole
    have hw c (hc : c ∈ padded.take whole) := h.numeral c (List.mem_of_mem_take hc)
    have hf c (hc : c ∈ padded.drop whole) := h.numeral c (List.mem_of_mem_drop hc)
    have chars := unpoint_no_sign hw hf
    simp [trim_of_forall (signed_no_whitespace _ fun c hc => (chars c hc).1),
      sign_signed _ fun c hc => (chars c hc).2, point_unpoint hw hf, h.value_eq,
      unsign_natAbs, Decimal.normalize_self, show padded.length - whole = value.exponent by omega]

theorem length_pad_digits {n : Nat} (h : n < 100) : (pad 2 (digits n)).length = 2 := by
  rw [digits]
  split
  · simp [pad]
  · rw [digits]
    simp [pad, show n / 10 < 10 by omega]

open Std.Time in
/-- ISO 8601 `YYYY-MM-DD`; other years have more digits or a minus sign. -/
def Date.chars (date : PlainDate) : List Char :=
  let year : Int := date.year
  signed year (pad 4 (digits year.natAbs)) ++
    '-' :: pad 2 (digits date.month.val.toNat) ++ '-' :: pad 2 (digits date.day.val.toNat)

open Std.Time in
def Date.ofChars? (chars : List Char) : Option PlainDate :=
  match chars.reverse with
  | day₂ :: day₁ :: separator₂ :: month₂ :: month₁ :: separator₁ :: year =>
    if separator₁ = '-' ∧ separator₂ = '-' then
      let (negative, year) := sign year.reverse
      match value year, value [month₁, month₂], value [day₁, day₂] with
      | some y, some m, some d =>
        if 4 ≤ year.length then
          if hm : 1 ≤ (m : Int) ∧ (m : Int) ≤ 12 then
            if hd : 1 ≤ (d : Int) ∧ (d : Int) ≤ 31 then
              let year : Year.Offset := unsign negative y
              if valid : (d : Int) ≤ (Month.Ordinal.days year.isLeap ⟨m, hm⟩).val then
                some ⟨year, ⟨m, hm⟩, ⟨d, hd⟩, valid⟩
              else none
            else none
          else none
        else none
      | _, _, _ => none
    else none
  | _ => none

open Std.Time in
theorem Date.ofChars?_chars (date : PlainDate) : Date.ofChars? (Date.chars date) = some date := by
  obtain ⟨year, ⟨month, hm1, hm2⟩, ⟨day, hd1, hd2⟩, valid⟩ := date
  have hy := digits_valid (year : Int).natAbs 4
  have hyl := length_pad 4 (digits (year : Int).natAbs)
  have hm := digits_valid month.toNat 2
  have hd := digits_valid day.toNat 2
  have hml := length_pad_digits (n := month.toNat) (by omega)
  have hdl := length_pad_digits (n := day.toNat) (by omega)
  generalize hM : pad 2 (digits month.toNat) = M at hm hml
  generalize hD : pad 2 (digits day.toNat) = D at hd hdl
  match M, D, hml, hdl with
  | [m₁, m₂], [d₁, d₂], _, _ =>
  simp only [Date.chars, hM, hD]
  unfold Date.ofChars?
  simp [List.reverse_append, sign_signed _ fun c hc => (hy.numeral c hc).2.1, hy.value_eq,
    hm.value_eq, hd.value_eq, hyl, unsign_natAbs, Int.toNat_of_nonneg (by omega : 0 ≤ month),
    Int.toNat_of_nonneg (by omega : 0 ≤ day), hm1, hm2, hd1, hd2]
  exact valid

open Std.Time in
theorem Date.chars_no_whitespace (date : PlainDate) :
    ∀ c ∈ Date.chars date, jsWhitespace c = false := by
  simp only [Date.chars, List.forall_mem_append, List.forall_mem_cons]
  exact ⟨⟨signed_no_whitespace _ (digits_valid _ 4).no_whitespace, rfl,
    (digits_valid _ 2).no_whitespace⟩, rfl, (digits_valid _ 2).no_whitespace⟩

open Std.Time in
/-- What `<input type="date">` produces. -/
def date : Format PlainDate where
  kind := .date
  print date := String.ofList (Date.chars date)
  parse text := match Date.ofChars? (trim text.toList) with
    | some date => .ok date
    | none => .error "Enter a date as YYYY-MM-DD."
  parse_print date := by
    simp [String.toList_ofList, trim_of_forall (Date.chars_no_whitespace date), Date.ofChars?_chars]

theorem Uuid.canonicalFrom_mem :
    ∀ {chars : List Char} {position : Nat}, Uuid.canonicalFrom chars position = true →
      ∀ c ∈ chars, c ∈ '-' :: Uuid.hexDigits
  | [], _, _, c, hc => by simp at hc
  | _ :: _, _, h, c, hc => by
    simp only [Uuid.canonicalFrom, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hc with rfl | hc
    · split at h <;> simp_all
    · exact canonicalFrom_mem h.2 c hc

def uuid : Format Uuid where
  kind := .uuid
  print := Uuid.value
  parse text :=
    let lowered := String.ofList ((trim text.toList).map Char.toLower)
    if h : Uuid.isCanonical lowered then .ok ⟨lowered, h⟩
    else .error "Enter a UUID, such as 123e4567-e89b-12d3-a456-426614174000."
  parse_print uuid := by
    obtain ⟨value, canonical⟩ := uuid
    have facts : ∀ c ∈ '-' :: Uuid.hexDigits, jsWhitespace c = false ∧ c.toLower = c := by
      decide
    have facts c (hc : c ∈ value.toList) := facts c (Uuid.canonicalFrom_mem canonical c hc)
    have lower : value.toList.map Char.toLower = value.toList := by
      simpa using List.map_congr_left (fun c hc => (facts c hc).2)
    simp [trim_of_forall fun c hc => (facts c hc).1, lower, canonical]

/-- Blank text is `none`; `blank` rules out the inner format reading it as a value. -/
def optional
    {α : Type}
    (format : Format α)
    (blank : (format.parse "").isOk = false)
    : Format (Option α) where
  kind := format.kind
  print
    | none => ""
    | some value => format.print value
  parse text := match format.parse text with
    | .ok value => .ok (some value)
    | .error error => if (trim text.toList).isEmpty then .ok none else .error error
  parse_print
    | none => by
      cases h : format.parse "" with
      | ok => simp [h, Except.isOk, Except.toBool] at blank
      | error => simp; rfl
    | some value => by simp [format.parse_print]

@[instance_reducible]
def toJson {α : Type} (format : Format α) : ToJson α :=
  ⟨(.str <| format.print ·)⟩

@[instance_reducible]
def fromJson {α : Type} (format : Format α) : FromJson α :=
  ⟨fun
    | .str text => format.parse text
    | _ => .error "String expected"⟩

theorem fromJson_toJson {α : Type} (format : Format α) (value : α) :
    format.fromJson.fromJson? (format.toJson.toJson value) = .ok value :=
  format.parse_print value

end Format

instance : ToString Decimal := ⟨Format.decimal.print⟩

-- Strings, because JavaScript numbers lose digits beyond 2^53.
instance : ToJson Decimal := Format.decimal.toJson
instance : FromJson Decimal := Format.decimal.fromJson
instance : ToJson Int64 := Format.int64.toJson
instance : FromJson Int64 := Format.int64.fromJson

instance : ToJson Std.Time.PlainDate := Format.date.toJson
instance : FromJson Std.Time.PlainDate := Format.date.fromJson

instance : ToJson Uuid := Format.uuid.toJson
instance : FromJson Uuid := Format.uuid.fromJson

end Forms.Model
