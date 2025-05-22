import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example : ¬o.isSome ↔ o = none := by
  cases o <;> simp [isSome]

/- ACTUAL PROOF OF Option.not_isSome_iff_eq_none -/

example : ¬o.isSome ↔ o = none := by
  cases o <;> simp