import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x : Bool}, true ≤ x → x = true := by
  intro x h
  cases x
  case tt =>
    exact rfl
  case ff =>
    exfalso
    apply h
    apply Bool.le_refl

/- ACTUAL PROOF OF Bool.eq_true_of_true_le -/

example : ∀ {x : Bool}, true ≤ x → x = true := by
  decide