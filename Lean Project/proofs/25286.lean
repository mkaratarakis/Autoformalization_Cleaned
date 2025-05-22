import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (b = (a || b)) ↔ (a → b) := by
  decide

/- ACTUAL PROOF OF Bool.iff_or_self -/

example : ∀(a b : Bool), (b = (a || b)) ↔ (a → b) := by
  decide