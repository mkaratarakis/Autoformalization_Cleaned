import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), (!x || x) = true := by
  intro x
  cases x
  · calc
      !x || x
    = true || false := by rfl
    = true := by rfl
  · calc
      !x || x
    = false || true := by rfl
    = true := by rfl

/- ACTUAL PROOF OF Bool.not_or_self -/

example : ∀ (x : Bool), (!x || x) = true := by
  decide