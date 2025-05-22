import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y : Bool), ((!x) != (!y)) = (x != y) := by
  intro x y
  cases x
  · cases y
    · simp
    · simp
  · cases y
    · simp
    · simp

/- ACTUAL PROOF OF Bool.not_bne_not -/

example : ∀ (x y : Bool), ((!x) != (!y)) = (x != y) := by
  decide