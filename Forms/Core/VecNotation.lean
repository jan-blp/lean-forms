import Mathlib.Data.Fin.VecNotation

namespace Forms.DependentVec

/-- Vector notation for entries whose types depend on their index. -/
scoped macro "![" entries:term,* "]" : term => do
  let mut result ← `(fun i => nomatch i)
  for entry in entries.getElems.reverse do
    result ← `(Fin.cons $entry $result)
  return result

end Forms.DependentVec
