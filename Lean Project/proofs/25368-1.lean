import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y : Bool), x ≤ y ∨ y ≤ x := by
  intros x y
  cases x
  · cases y
    · left; refl
    · right; exact le_top
  · cases y
    · left; exact bot_le
    · left; refl

/- ACTUAL PROOF OF Bool.le_total -/

example : ∀ (x y : Bool), x ≤ y ∨ y ≤ x := by
  decide