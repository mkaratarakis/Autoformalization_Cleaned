import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), false ≤ x := by
  intro x
  cases x
  · exact le_refl
  · exact le_top

/- ACTUAL PROOF OF Bool.false_le -/

example : ∀ (x : Bool), false ≤ x := by
  decide