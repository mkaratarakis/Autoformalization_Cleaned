import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x ≤ y → x ≠ y → x < y := by
  intros x y hle hne
  cases x
  · cases y
    · exact False.elim (hne rfl)
    · exact hle
  · cases y
    · exact False.elim (hne rfl)
    · exact False.elim (hle (by rfl))

/- ACTUAL PROOF OF Bool.lt_of_le_of_ne -/

example : ∀ {x y : Bool}, x ≤ y → x ≠ y → x < y := by
  decide