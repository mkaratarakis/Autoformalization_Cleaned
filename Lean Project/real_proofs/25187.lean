import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option



example : x.join ≠ none ↔ ∃ z, x = some (some z) := by
  simp only [ne_none_iff_exists', join_eq_some, iff_self]