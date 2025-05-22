import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x ≤ y → x ≠ y → x < y := by
  intros x y hle hne
  cases x
  · cases y
    · exact hne rfl
    · assumption
  · cases y
    · exact hne rfl
    · apply hne
      apply hle
      refl

/- ACTUAL PROOF OF Bool.lt_of_le_of_ne -/

example : ∀ {x y : Bool}, x ≤ y → x ≠ y → x < y := by
  decide