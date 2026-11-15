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
  cases chars with
  | nil => rfl
  | cons c rest => simp [List.dropWhile, h c (by simp)]

theorem dropWhile_of_all
    {p : Char → Bool}
    {chars : List Char}
    (h : ∀ c ∈ chars, p c = true)
    : chars.dropWhile p = [] := by
  induction chars with
  | nil => rfl
  | cons c rest ih => simp_all [List.dropWhile]

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

theorem digit_facts : ∀ d : Fin 10,
    digitValue (digit d) = some d ∧ jsWhitespace (digit d) = false ∧
      digit d ≠ '-' ∧ digit d ≠ '.' := by
  decide

theorem digitValue_digit {d : Nat} (h : d < 10) : digitValue (digit d) = some d :=
  (digit_facts ⟨d, h⟩).1

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

theorem length_digits {n : Nat} (h : n < 100) : (digits n).length ≤ 2 := by
  rw [digits]
  split
  · simp
  · rw [digits]
    simp [show n / 10 < 10 by omega]

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

theorem valueReversed_append_zeros (chars : List Char) (count : Nat) :
    valueReversed (chars ++ List.replicate count (digit 0)) = valueReversed chars := by
  induction chars with
  | nil =>
    induction count with
    | zero => rfl
    | succ count ih =>
      simp only [List.nil_append, valueReversed] at ih
      simp [List.replicate_succ, valueReversed, ih, digitValue_digit (show 0 < 10 by decide)]
  | cons c rest ih => simp [valueReversed, ih]

/-- Characters that are all digits, with value `n`. -/
def Digits (chars : List Char) (n : Nat) : Prop :=
  value chars = some n ∧ chars ≠ [] ∧ ∀ c ∈ chars, ∃ d : Fin 10, c = digit d

theorem digits_valid (n : Nat) (width : Nat) : Digits (pad width (digits n)) n := by
  refine ⟨?_, by simp [pad, digits_ne_nil], ?_⟩
  · have := digits_ne_nil n
    simp [value, pad, this, List.reverse_append, List.reverse_replicate,
      valueReversed_append_zeros, valueReversed_digits]
  · intro c h
    rcases List.mem_append.1 h with h | h
    · exact ⟨0, (List.eq_of_mem_replicate h)⟩
    · exact digits_digit c h

theorem Digits.no_whitespace {chars : List Char} {n : Nat} (h : Digits chars n) :
    ∀ c ∈ chars, jsWhitespace c = false := by
  intro c hc
  obtain ⟨d, rfl⟩ := h.2.2 c hc
  exact (digit_facts d).2.1

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
    have h := digits_valid n 0
    simp only [pad, Nat.zero_sub, List.replicate_zero, List.nil_append] at h
    simp [String.toList_ofList, trim_of_forall h.no_whitespace, h.1]

def sign : List Char → Bool × List Char
  | c :: rest => if c = '-' then (true, rest) else (false, c :: rest)
  | [] => (false, [])

def signed (value : Int) (chars : List Char) : List Char :=
  if value < 0 then '-' :: chars else chars

def unsign (negative : Bool) (n : Nat) : Int :=
  if negative then -n else n

theorem sign_signed {chars : List Char} (value : Int) (h : ∀ c ∈ chars.head?, c ≠ '-') :
    sign (signed value chars) = (decide (value < 0), chars) := by
  unfold signed
  split
  · simp_all [sign]
  · cases chars with
    | nil => simp_all [sign]
    | cons c rest => simp_all [sign]

theorem Digits.head {chars : List Char} {n : Nat} (h : Digits chars n) :
    ∀ c ∈ chars.head?, c ≠ '-' := by
  intro c hc
  obtain ⟨d, rfl⟩ := h.2.2 c (List.mem_of_mem_head? hc)
  exact (digit_facts d).2.2.1

theorem unsign_natAbs (value : Int) : unsign (decide (value < 0)) value.natAbs = value := by
  unfold unsign
  split <;> simp_all <;> omega

theorem signed_no_whitespace
    {chars : List Char}
    (value : Int)
    (h : ∀ c ∈ chars, jsWhitespace c = false)
    : ∀ c ∈ signed value chars, jsWhitespace c = false := by
  unfold signed
  split
  · simpa [jsWhitespace] using h
  · exact h

def integer : Format Int where
  kind := .integer
  print n := String.ofList (signed n (digits n.natAbs))
  parse text :=
    let (negative, chars) := sign (trim text.toList)
    match value chars with
    | some n => .ok (unsign negative n)
    | none => .error "Enter a whole number."
  parse_print n := by
    have h := digits_valid n.natAbs 0
    simp only [pad, Nat.zero_sub, List.replicate_zero, List.nil_append] at h
    simp [String.toList_ofList, trim_of_forall (signed_no_whitespace n h.no_whitespace),
      sign_signed n h.head, h.1, unsign_natAbs]

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

theorem Digits.no_point {chars : List Char} {n : Nat} (h : Digits chars n) :
    ∀ c ∈ chars, (c != '.') = true := by
  intro c hc
  obtain ⟨d, rfl⟩ := h.2.2 c hc
  simpa using (digit_facts d).2.2.2

theorem length_pad (width : Nat) (chars : List Char) : width ≤ (pad width chars).length := by
  simp [pad]
  omega

/-- The digits before and after an optional decimal point. -/
def point (chars : List Char) : Option (List Char × List Char) :=
  match chars.dropWhile (· != '.') with
  | [] => some (chars, [])
  | _ :: fraction =>
    if fraction.contains '.' then none else some (chars.takeWhile (· != '.'), fraction)

def Decimal.chars (value : Decimal) : List Char :=
  let padded := pad (value.exponent + 1) (digits value.mantissa.natAbs)
  let whole := padded.length - value.exponent
  signed value.mantissa
    (if value.exponent = 0 then padded else padded.take whole ++ '.' :: padded.drop whole)

theorem point_digits {chars : List Char} {n : Nat} (h : Digits chars n) :
    point chars = some (chars, []) := by
  have : chars.dropWhile (· != '.') = [] := dropWhile_of_all h.no_point
  simp [point, this]

theorem point_split
    {whole fraction : List Char}
    (hw : ∀ c ∈ whole, (c != '.') = true)
    (hf : ∀ c ∈ fraction, (c != '.') = true)
    : point (whole ++ '.' :: fraction) = some (whole, fraction) := by
  have : '.' ∉ fraction := fun hm => by simpa using hf '.' hm
  simp [point, List.dropWhile_append_of_pos hw, List.takeWhile_append_of_pos hw, this]

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
    obtain ⟨mantissa, exponent, normalized⟩ := value
    have h := digits_valid mantissa.natAbs (exponent + 1)
    have hlen := length_pad (exponent + 1) (digits mantissa.natAbs)
    generalize hp : pad (exponent + 1) (digits mantissa.natAbs) = padded at h hlen
    have hself := Decimal.normalize_self ⟨mantissa, exponent, normalized⟩
    simp only at hself
    by_cases he : exponent = 0
    · subst he
      have body : Decimal.chars ⟨mantissa, 0, normalized⟩ = signed mantissa padded := by
        simp [Decimal.chars, hp]
      simp only [body, String.toList_ofList,
        trim_of_forall (signed_no_whitespace _ h.no_whitespace), sign_signed _ h.head,
        point_digits h, List.append_nil, h.1, List.length_nil, unsign_natAbs, hself]
    · generalize hw : padded.length - exponent = whole
      have body : Decimal.chars ⟨mantissa, exponent, normalized⟩ =
          signed mantissa (padded.take whole ++ '.' :: padded.drop whole) := by
        simp [Decimal.chars, hp, he, ← hw]
      have chars : ∀ c ∈ padded.take whole ++ '.' :: padded.drop whole,
          jsWhitespace c = false ∧ c ≠ '-' := by
        intro c hc
        simp only [List.mem_append, List.mem_cons] at hc
        rcases hc with hc | rfl | hc
        · obtain ⟨d, rfl⟩ := h.2.2 c (List.mem_of_mem_take hc)
          exact ⟨(digit_facts d).2.1, (digit_facts d).2.2.1⟩
        · decide
        · obtain ⟨d, rfl⟩ := h.2.2 c (List.mem_of_mem_drop hc)
          exact ⟨(digit_facts d).2.1, (digit_facts d).2.2.1⟩
      have length : (padded.drop whole).length = exponent := by
        simp [← hw]
        omega
      simp only [body, String.toList_ofList,
        trim_of_forall (signed_no_whitespace _ fun c hc => (chars c hc).1),
        sign_signed _ fun c hc => (chars c (List.mem_of_mem_head? hc)).2,
        point_split (fun c hc => h.no_point c (List.mem_of_mem_take hc))
          (fun c hc => h.no_point c (List.mem_of_mem_drop hc)),
        List.take_append_drop, h.1, length, unsign_natAbs, hself]

theorem length_pad_digits {n : Nat} (h : n < 100) : (pad 2 (digits n)).length = 2 := by
  have := length_digits h
  simp [pad]
  omega

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
  obtain ⟨year, month, day, valid⟩ := date
  obtain ⟨month, hm1, hm2⟩ := month
  obtain ⟨day, hd1, hd2⟩ := day
  have hy := digits_valid (year : Int).natAbs 4
  have hyl := length_pad 4 (digits (year : Int).natAbs)
  have hm := digits_valid month.toNat 2
  have hd := digits_valid day.toNat 2
  have hml := length_pad_digits (n := month.toNat) (by omega)
  have hdl := length_pad_digits (n := day.toNat) (by omega)
  generalize hY : pad 4 (digits (year : Int).natAbs) = Y at hy hyl
  generalize hM : pad 2 (digits month.toNat) = M at hm hml
  generalize hD : pad 2 (digits day.toNat) = D at hd hdl
  match M, D, hml, hdl with
  | [m₁, m₂], [d₁, d₂], _, _ =>
  simp only [Date.chars, hY, hM, hD]
  unfold Date.ofChars?
  simp [List.reverse_append, sign_signed _ hy.head, hy.1, hm.1, hd.1, hyl, unsign_natAbs,
    Int.toNat_of_nonneg (by omega : 0 ≤ month), Int.toNat_of_nonneg (by omega : 0 ≤ day), hm1, hm2,
    hd1, hd2]
  exact valid

open Std.Time in
theorem Date.chars_no_whitespace (date : PlainDate) :
    ∀ c ∈ Date.chars date, jsWhitespace c = false := by
  intro c hc
  simp only [Date.chars, List.mem_append, List.mem_cons] at hc
  rcases hc with (hc | rfl | hc) | rfl | hc
  · exact signed_no_whitespace _ (digits_valid _ 4).no_whitespace c hc
  · decide
  · exact (digits_valid _ 2).no_whitespace c hc
  · decide
  · exact (digits_valid _ 2).no_whitespace c hc

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
      ∀ c ∈ chars, c = '-' ∨ Uuid.hexDigit c = true
  | [], _, _, c, hc => by simp at hc
  | _ :: _, _, h, c, hc => by
    simp only [Uuid.canonicalFrom, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hc with rfl | hc
    · split at h <;> simp_all
    · exact canonicalFrom_mem h.2 c hc

theorem Uuid.char_facts {c : Char} (h : c = '-' ∨ Uuid.hexDigit c = true) :
    jsWhitespace c = false ∧ c.toLower = c := by
  rcases h with rfl | h
  · decide
  · simp only [Uuid.hexDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    have upper : ¬ (c.val ≥ 'A'.val ∧ c.val ≤ 'Z'.val) := by
      have a : 'A'.val.toNat = 65 := rfl
      have z : 'Z'.val.toNat = 90 := rfl
      simp only [ge_iff_le, UInt32.le_iff_toNat_le, a, z]
      simp only [Char.toNat] at h
      omega
    constructor
    · simp [jsWhitespace]
      omega
    · unfold Char.toLower
      split
      · contradiction
      · rfl

def uuid : Format Uuid where
  kind := .uuid
  print := Uuid.value
  parse text :=
    let lowered := String.ofList ((trim text.toList).map Char.toLower)
    if h : Uuid.isCanonical lowered then .ok ⟨lowered, h⟩
    else .error "Enter a UUID, such as 123e4567-e89b-12d3-a456-426614174000."
  parse_print uuid := by
    obtain ⟨value, canonical⟩ := uuid
    have facts c (hc : c ∈ value.toList) := Uuid.char_facts (Uuid.canonicalFrom_mem canonical c hc)
    have lower : value.toList.map Char.toLower = value.toList :=
      (List.map_congr_left fun c hc => (facts c hc).2).trans (List.map_id _)
    simp [trim_of_forall fun c hc => (facts c hc).1, lower, canonical]

end Format

instance : ToString Decimal := ⟨Format.decimal.print⟩

instance : ToJson Std.Time.PlainDate := ⟨(.str <| Format.date.print ·)⟩

instance : FromJson Std.Time.PlainDate := ⟨fun json => do Format.date.parse (← json.getStr?)⟩

instance : ToJson Uuid := ⟨(.str ·.value)⟩

instance : FromJson Uuid := ⟨fun json => do Format.uuid.parse (← json.getStr?)⟩

end Forms.Model
