import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), x ≤ true := by
  intro x
  cases x
  · exact Or.inr rfl
  · exact Or.inl rfl

/- ACTUAL PROOF OF Bool.le_true -/

example : ∀ (x : Bool), x ≤ true := by
  decide