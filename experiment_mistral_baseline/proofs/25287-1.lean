import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), (!x || x) = true := by
  intro x
  cases x
  · calc
      (!false || false)
        = (true || false) := by rfl
        = true := by rfl
  · calc
      (!true || true)
        = (false || true) := by rfl
        = true := by rfl

/- ACTUAL PROOF OF Bool.not_or_self -/

example : ∀ (x : Bool), (!x || x) = true := by
  decide