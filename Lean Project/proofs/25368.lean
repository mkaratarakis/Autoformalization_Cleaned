import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y : Bool), x ≤ y ∨ y ≤ x := by
  intros x y
  cases x
  · cases y
    · left; trivial
    · left; trivial
  · cases y
    · right; trivial
    · left; trivial

/- ACTUAL PROOF OF Bool.le_total -/

example : ∀ (x y : Bool), x ≤ y ∨ y ≤ x := by
  decide