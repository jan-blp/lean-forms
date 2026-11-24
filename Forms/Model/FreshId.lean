module

public import Forms.Model.Scalar
public import Mathlib.Data.List.SplitLengths

/-!
# Fresh item ids

New collection items get their UUIDs from a `MonadFreshId`, which is `Supply` at runtime.

The *only* requirement is that the generated UUIDs are unique. Nothing relies on them being
unpredictable or statistically random.

`Supply` is a xoshiro256** generator, following the reference implementation at
<https://prng.di.unimi.it/xoshiro256starstar.c> (Blackman and Vigna,
"Scrambled Linear Pseudorandom Number Generators", <https://doi.org/10.1145/3460772>).

Notes:
- Pure algorithm that depends on external seed.
- It uses only `UInt64` arithmetic, which is fast in 32-bit Wasm.
- Its 256-bit state uses the whole seed (32 bytes, sent as 64 hexadecimal digits).
- It is *NOT* cryptographically secure.
-/

@[expose] public section
namespace Forms.Model

def Uuid.hexDigit (digit : Fin 16) : Char :=
  Uuid.hexDigits[digit.val]'(by simp [Uuid.hexDigits])

theorem Uuid.hexDigit_mem (digit : Fin 16) : Uuid.hexDigit digit ∈ Uuid.hexDigits :=
  List.getElem_mem _

theorem Uuid.canonicalFrom_hex
  {digits : List (Fin 16)}
  {rest : List Char}
  {position : Nat}
  (apart : ∀ offset < digits.length, position + offset ∉ [8, 13, 18, 23])
  : Uuid.canonicalFrom (digits.map Uuid.hexDigit ++ rest) position =
    Uuid.canonicalFrom rest (position + digits.length) := by
  induction digits generalizing position with
  | nil => simp
  | cons digit digits ih =>
    have here : position ∉ [8, 13, 18, 23] := by simpa using apart 0 (by simp)
    have later := ih (position := position + 1) fun offset bound => by
      rw [show position + 1 + offset = position + (offset + 1) by omega]
      exact apart (offset + 1) (by simpa using bound)
    simp [Uuid.canonicalFrom, here, later, Uuid.hexDigit_mem, Nat.add_assoc, Nat.add_comm 1]

/-- Prints 32 hexadecimal digits in the 8-4-4-4-12 form. -/
def Uuid.ofDigits (digits : Vector (Fin 16) 32) : Uuid where
  value := String.ofList <| ['-'].intercalate <|
    ([8, 4, 4, 4, 12].splitLengths digits.toList).map (·.map Uuid.hexDigit)
  canonical := by
    simp only [Uuid.isCanonical, String.toList_ofList, List.splitLengths, List.splitAt_eq,
      List.map, List.intercalate, List.intersperse, List.flatten, List.append_eq,
      List.cons_append, List.nil_append]
    repeat
      rw [Uuid.canonicalFrom_hex (by simp; decide)]
      simp only [List.length_take, List.length_drop, Vector.length_toList, Uuid.canonicalFrom]
    decide

/-- A fixed id ending in `n`, for example data. Real items get theirs from the server or a
`Supply`. -/
def Uuid.ofNat (n : Nat) : Uuid :=
  Uuid.ofDigits <| Vector.ofFn fun index =>
    if index.val = 12 then 4
    else if index.val = 16 then 8
    else if index.val < 20 then 0
    else Fin.ofNat 16 (n >>> (4 * (31 - index.val)))

/-- Monads that can hand out new item ids. -/
class MonadFreshId (m : Type → Type) where
  freshId : m Uuid

export MonadFreshId (freshId)

/-- The xoshiro256** generator state; see the module docstring. -/
structure Supply where
  first : UInt64
  second : UInt64
  third : UInt64
  fourth : UInt64
  deriving BEq, Repr

structure Supply.Word where
  value : UInt64
  supply : Supply

structure Supply.Drawn where
  id : Uuid
  supply : Supply

def Supply.rotateLeft (word : UInt64) (count : UInt64) : UInt64 :=
  (word <<< count) ||| (word >>> (64 - count))

def Supply.word (supply : Supply) : Supply.Word :=
  let value := rotateLeft (supply.second * 5) 7 * 9
  let third := supply.third ^^^ supply.first
  let fourth := supply.fourth ^^^ supply.second
  let second := supply.second ^^^ third
  let first := supply.first ^^^ fourth
  { value
    supply := {
      first
      second
      third := third ^^^ (supply.second <<< 17)
      fourth := rotateLeft fourth 45 } }

/-- The first outputs of the reference implementation, seeded with `1, 2, 3, 4`. -/
theorem Supply.word_reference :
    let first := Supply.word { first := 1, second := 2, third := 3, fourth := 4 }
    let second := first.supply.word
    let third := second.supply.word
    let fourth := third.supply.word
    [first.value, second.value, third.value, fourth.value] =
      [11520, 0, 1509978240, 1215971899390074240] := by
  decide

def Supply.nibble (word : UInt64) (index : Fin 16) : Fin 16 :=
  Fin.ofNat 16 ((word >>> (4 * (15 - index.val)).toUInt64) &&& 15).toNat

/-- A random version 4 UUID. -/
def Supply.next (supply : Supply) : Supply.Drawn :=
  let high := supply.word
  let low := high.supply.word
  let raw (index : Fin 32) : Fin 16 :=
    if early : index.val < 16 then nibble high.value ⟨index.val, early⟩
    else nibble low.value ⟨index.val - 16, by omega⟩
  let digit (index : Fin 32) : Fin 16 :=
    if index.val = 12 then 4
    else if index.val = 16 then 8 + raw index % 4
    else raw index
  { id := Uuid.ofDigits (Vector.ofFn digit), supply := low.supply }

instance {m : Type → Type} [Monad m] : MonadFreshId (StateT Supply m) where
  freshId := modifyGet fun supply =>
    let drawn := supply.next
    (drawn.id, drawn.supply)

def Supply.hexValue (character : Char) : Option Nat :=
  Uuid.hexDigits.idxOf? character.toLower

def Supply.wordOf (digits : List Nat) : UInt64 :=
  digits.foldl (fun word digit => word * 16 + digit.toUInt64) 0

/-- Reads 64 hexadecimal digits. -/
def Supply.ofSeed? (seed : String) : Option Supply := do
  let digits ← seed.toList.mapM hexValue
  unless digits.length == 64 && digits.any (· != 0) do none
  pure {
    first := wordOf (digits.take 16)
    second := wordOf ((digits.drop 16).take 16)
    third := wordOf ((digits.drop 32).take 16)
    fourth := wordOf (digits.drop 48) }

end Forms.Model
