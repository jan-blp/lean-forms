module

public import Forms.Model.Scalar

@[expose] public section
namespace Forms.Model

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

/-- The whitespace accepted by JavaScript's String.trim. -/
def Format.whitespace (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n && n ≤ 0x0D) || n == 0x20 || n == 0xA0 || n == 0x1680 ||
    (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 ||
    n == 0x202F || n == 0x205F || n == 0x3000 || n == 0xFEFF

def Format.trim (text : String) : String :=
  ((text.dropWhile whitespace).dropEndWhile whitespace).toString

def Format.plain : Format String where
  kind := .plain
  print := id
  parse := .ok

def Format.natural : Format Nat where
  kind := .natural
  print := toString
  parse text :=
    let text := trim text
    match if text.all Char.isDigit then text.toNat? else none with
    | some value => .ok value
    | none => .error "Enter a non-negative whole number."

def Format.integer : Format Int where
  kind := .integer
  print := toString
  parse text :=
    let text := trim text
    let (negative, digits) :=
      if text.startsWith "-" then (true, (text.drop 1).toString) else (false, text)
    match if !digits.isEmpty && digits.all Char.isDigit then digits.toNat? else none with
    | some value => .ok (if negative then -value else value)
    | none => .error "Enter a whole number."

def Format.refine
  {α β : Type}
  (format : Format α)
  (print : β → α)
  (parse : α → Option β)
  (message : String)
  : Format β where
  kind := format.kind
  print value := format.print (print value)
  parse text := do
    match parse (← format.parse text) with
    | some value => .ok value
    | none => .error message

def Format.int32 : Format Int32 :=
  integer.refine Int32.toInt Int32.ofInt? "Enter a whole number between -2147483648 and 2147483647."

def Format.int64 : Format Int64 :=
  integer.refine Int64.toInt Int64.ofInt?
    "Enter a whole number between -9223372036854775808 and 9223372036854775807."

def Format.decimal : Format Decimal where
  kind := .decimal
  print := Decimal.toString
  parse text :=
    let text := trim text
    let (negative, unsigned) :=
      if text.startsWith "-" then (true, (text.drop 1).toString) else (false, text)
    let (whole, fraction) := match unsigned.splitOn "." with
      | [whole] => (whole, some "")
      | [whole, fraction] => (whole, some fraction)
      | _ => ("", none)
    let digits := whole ++ fraction.getD ""
    let mantissa := if !digits.isEmpty && digits.all Char.isDigit then digits.toNat? else none
    match fraction, mantissa with
    | some fraction, some mantissa =>
      .ok (Decimal.normalize (if negative then -mantissa else mantissa) fraction.length)
    | _, _ => .error "Enter a decimal number, such as 12.50."

/-- What `<input type="date">` produces. -/
def Format.date : Format Std.Time.PlainDate where
  kind := .date
  print := Date.toIso
  parse text := match Date.ofIso? (trim text) with
    | some date => .ok date
    | none => .error "Enter a date as YYYY-MM-DD."

def Format.uuid : Format Uuid where
  kind := .uuid
  print := Uuid.value
  parse text := match Uuid.ofString? (trim text) with
    | some uuid => .ok uuid
    | none => .error "Enter a UUID, such as 123e4567-e89b-12d3-a456-426614174000."

end Forms.Model
