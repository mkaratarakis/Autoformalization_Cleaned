import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), (!x || x) = true := by
  intro x
  cases x
  · calc
      !false || false
    = true := by simp [not, or]
  · calc
      !true || true
    = true := by simp [not, or]

/- ACTUAL PROOF OF Bool.not_or_self -/

example : ∀ (x : Bool), (!x || x) = true := by
  decide