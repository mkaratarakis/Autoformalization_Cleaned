import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), x ≤ x := by
  intro x
  exact le_refl x

/- ACTUAL PROOF OF Bool.le_refl -/

example : ∀ (x : Bool), x ≤ x := by
  decide