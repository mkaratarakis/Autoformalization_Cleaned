import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), ¬ x < x := by
  intro x
  cases x
  . simp [lt]
  . simp [lt]

/- ACTUAL PROOF OF Bool.lt_irrefl -/

example : ∀ (x : Bool), ¬ x < x := by
  decide