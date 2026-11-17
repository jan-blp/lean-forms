module

public import Forms.Model.Item
public import Forms.Model.Supply

@[expose] public section
namespace Tests
open Forms.Model

/-- A fixed seed, so new item ids are the same on every run. -/
def supply : Supply := { first := 1, second := 2, third := 3, fourth := 4 }

def firstId : Uuid := .ofNat 1
def secondId : Uuid := .ofNat 2
def thirdId : Uuid := .ofNat 3

end Tests
