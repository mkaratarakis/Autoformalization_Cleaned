import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x : Bool}, x ≤ false → x = false := by
  intro x h
  cases x
  · rfl
  · exfalso
    apply not_le_of_gt h
    exact ff_lt_tt

/- ACTUAL PROOF OF Bool.eq_false_of_le_false -/

example : ∀ {x : Bool}, x ≤ false → x = false := by
  decide