import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example : o ≠ none ↔ ∃ x, some x = o := by
  cases o with
  | none =>
    simp only [Ne.def, not_false_iff, exists_prop]
    exact iff_of_false (by simp) (by simp)
  | some x =>
    simp only [Ne.def, exists_prop, exists_eq_left']
    exact iff_of_true (by simp) (by simp)

/- ACTUAL PROOF OF Option.ne_none_iff_exists -/

example : o ≠ none ↔ ∃ x, some x = o := by
  cases o <;> simp