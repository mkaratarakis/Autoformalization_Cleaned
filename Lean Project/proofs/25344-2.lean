import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), false ≤ x := by
  intro x
  cases x
  · apply le_refl
  · apply false_le_true

/- ACTUAL PROOF OF Bool.false_le -/

example : ∀ (x : Bool), false ≤ x := by
  decide