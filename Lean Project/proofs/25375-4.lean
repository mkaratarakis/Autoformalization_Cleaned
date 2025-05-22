import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x : Bool}, true ≤ x → x = true := by
  intro x h
  cases x
  · exact rfl
  · exfalso
    apply h
    apply (not_le_of_gt ff_lt_tt)

/- ACTUAL PROOF OF Bool.eq_true_of_true_le -/

example : ∀ {x : Bool}, true ≤ x → x = true := by
  decide