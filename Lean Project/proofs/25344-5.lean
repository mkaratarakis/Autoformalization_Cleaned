import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), false ≤ x := by
  intro x
  cases x
  · exact Bool.le_refl false
  · rfl

/- ACTUAL PROOF OF Bool.false_le -/

example : ∀ (x : Bool), false ≤ x := by
  decide