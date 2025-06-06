import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example : o ≠ none ↔ ∃ x, some x = o := by
  cases o with
  | none =>
    simp only [Ne.def, not_false_iff, isSome_none, exists_prop, exists_false]
    exact Iff.rfl
  | some x =>
    simp only [Ne.def, isSome_some, exists_prop, exists_eq_left']
    exact Iff.rfl

/- ACTUAL PROOF OF Option.ne_none_iff_exists -/

example : o ≠ none ↔ ∃ x, some x = o := by
  cases o <;> simp