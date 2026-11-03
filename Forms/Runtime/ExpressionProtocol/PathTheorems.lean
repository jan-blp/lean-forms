import Forms.Runtime.ExpressionProtocol
import Forms.Runtime.ExpressionProtocol.ValueTheorems

namespace Forms.Runtime.ExpressionProtocol
open Lean
set_option backward.isDefEq.respectTransparency false

private theorem path_decode_reindex {a b result : Schema} (h : a = b) (labels : List String)
    (path : Path b.dataType result.dataType)
    (decoded : pathFromLabels b labels = .ok ⟨result, path⟩) :
    pathFromLabels a labels =
      .ok ⟨result, cast (congrArg (fun s => Path s.dataType result.dataType) h).symm path⟩ := by
  cases h
  exact decoded

theorem path_decode {input result : DataType} (path : Path input result) :
    pathFromLabels (canonicalSchema input) path.toList =
      .ok ⟨canonicalSchema result, canonicalPath path⟩ := by
  induction path with
  | self => simp [Path.toList, pathFromLabels, canonicalPath, pure, Except.pure]
  | @field labels fields result i rest ih =>
      have found := find?_key (fun _ _ => labels.options_nodup.get_inj_iff.mp)
        (List.mem_finRange (enumIndex labels i))
      rw [enumIndex_label] at found
      simp only [Path.toList, canonicalSchema, pathFromLabels, findName, found]
      rw [path_decode_reindex (congrArg (fun j => canonicalSchema (fields j))
        ((enumIndex labels).symm_apply_apply i)) _ _ ih]
      simp only [Except.map, canonicalPath, Eq.mpr, eqRec_eq_cast]

end Forms.Runtime.ExpressionProtocol
