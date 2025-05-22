import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), x ≤ true := by
  intro x
  cases x
  · exact Bool.le_top
  · exact Bool.le_top

/- ACTUAL PROOF OF Bool.le_true -/

example : ∀ (x : Bool), x ≤ true := by
  decide