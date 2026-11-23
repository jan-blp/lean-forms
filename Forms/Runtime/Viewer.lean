module

public import Lean.Data.Json

@[expose] public section
namespace Forms.Runtime.Viewer

/-- An OCR cell, positioned in its page's units. -/
structure Cell where
  id : Nat
  x : Nat
  y : Nat
  width : Nat
  height : Nat
  text : String
  deriving Lean.ToJson, Lean.FromJson

structure Page where
  number : Nat
  width : Nat
  height : Nat
  cells : List Cell
  deriving Lean.ToJson, Lean.FromJson

structure Document where
  pages : List Page
  deriving Lean.ToJson, Lean.FromJson

end Forms.Runtime.Viewer
