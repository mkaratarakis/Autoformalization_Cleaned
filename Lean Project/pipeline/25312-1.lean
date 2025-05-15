import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), ((a && b) = b) ↔ (b → a) := by
  intros a b
  cases a <;> cases b <;> simp [and, implies]

/- ACTUAL PROOF OF Bool.and_iff_right_iff_imp -/

example : ∀(a b : Bool), ((a && b) = b) ↔ (b → a) := by
  decide