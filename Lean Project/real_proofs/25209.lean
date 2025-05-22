import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option



example : o ≠ none ↔ ∃ x, some x = o := by
  cases o <;> simp