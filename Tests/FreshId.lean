module

public import Forms.Model.Item
public import Forms.Model.FreshId

@[expose] public section
namespace Tests
open Forms.Model

/-- A fixed seed, so new item ids are the same on every run. -/
def supply : Supply := { first := 1, second := 2, third := 3, fourth := 4 }

def firstId : Uuid := .ofNat 1
def secondId : Uuid := .ofNat 2
def thirdId : Uuid := .ofNat 3

/-- Wraps values as items with the ids `firstId`, `secondId`, … -/
def items {α : Type} (values : List α) : List (Item α) :=
  IdGen.run (values.mapM Item.fresh)

private def seed : String := "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"

example : (Supply.ofSeed? seed).isSome := by decide
example : (Supply.ofSeed? (String.ofList (List.replicate 62 '1'))).isNone := by decide
example : (Supply.ofSeed? (String.ofList (List.replicate 64 '0'))).isNone := by decide

end Tests
