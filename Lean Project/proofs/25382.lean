import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, (!x) = (!y) ↔ x = y := by
  intros x y
  cases x <;> cases y <;> simp [not]

/- ACTUAL PROOF OF Bool.not_inj_iff -/

example : ∀ {x y : Bool}, (!x) = (!y) ↔ x = y := by
  decide