import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example : isSome x ↔ ∃ a, x = some a := by
  cases x
  case none =>
    simp only [isSome, exists_prop, exists_false, false_iff]
  case some val =>
    simp only [isSome, exists_prop, exists_eq_left]

/- ACTUAL PROOF OF Option.isSome_iff_exists -/

example : isSome x ↔ ∃ a, x = some a := by
  cases x <;> simp [isSome]