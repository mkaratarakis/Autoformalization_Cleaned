import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), x ≤ x := by
  intro x
  cases x <;> simp

/- ACTUAL PROOF OF Bool.le_refl -/

example : ∀ (x : Bool), x ≤ x := by
  decide