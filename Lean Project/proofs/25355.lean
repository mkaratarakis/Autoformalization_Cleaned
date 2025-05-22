import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), ¬ x < x := by
  intro x
  cases x
  · apply Not.intro
    simp
  · apply Not.intro
    simp

/- ACTUAL PROOF OF Bool.lt_irrefl -/

example : ∀ (x : Bool), ¬ x < x := by
  decide